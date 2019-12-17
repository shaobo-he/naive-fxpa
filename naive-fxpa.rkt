#lang typed/racket/base

(require
  (for-syntax racket/base
              racket/syntax
              syntax/parse))

(provide
 make-signature
 get-total-bw
 get-fb-bw
 get-ib-bw
 get-total-bits
 get-frac-bits
 bits->ufp
 bits->sfp
 get-fp-value
 get-fp-value-int
 get-fp-sign
 fp+
 fp-
 fp*
 fp/
 fp<
 fp<=
 fp>
 fp>=
 fp=
 ST
 WP
 RU
 RD
 ST?
 WP?
 RU?
 RD?)

(define-type Signature (Pairof Positive-Integer Natural))

(: make-signature (-> Positive-Integer Natural Signature))
(define (make-signature tb fb)
  (cons tb fb))

(: get-total-bw (-> Signature Positive-Integer))
(define (get-total-bw sig)
  (car sig))

(: get-total-bits (-> FixedPoint Positive-Integer))
(define (get-total-bits fb)
  (get-total-bw (FixedPoint-sig fb)))

(: get-frac-bits (-> FixedPoint Natural))
(define (get-frac-bits fb)
  (get-fb-bw (FixedPoint-sig fb)))

(: get-fb-bw (-> Signature Natural))
(define (get-fb-bw sig)
  (cdr sig))

(: get-fp-sign (-> FixedPoint Boolean))
(define (get-fp-sign fp)
  (SFixedPoint? fp))

(: get-ib-bw (-> Signature Natural))
(define (get-ib-bw sig)
  (define tb (get-total-bw sig))
  (define fb (get-fb-bw sig))
  (define ib (- tb fb))
  (cond
    [(>= ib 0) fb]
    [else (error "invalid fp signature")]))

(struct FixedPoint
  ([sig : Signature])
  #:transparent)

(struct UFixedPoint FixedPoint
  ([bits : Natural])
  #:transparent)

(struct SFixedPoint FixedPoint
  ([bits : Integer])
  #:transparent)

(: valid-range? (-> Signature Boolean Integer Boolean))
(define (valid-range? sig sign bits)
  (define tb (get-total-bw sig))
  (cond
    [(not sign)
     (and
      (>= bits 0)
      (< bits (expt 2 tb)))]
    [else
     (and
      (>= bits (- (expt 2 (- tb 1))))
      (< bits (expt 2 (- tb 1))))]))

(: bits->ufp (-> Natural Signature UFixedPoint))
(define (bits->ufp bits sig)
  (cond
    [(valid-range? sig #f bits) (UFixedPoint sig bits)]
    [else (error "not valid bits!")]))

(: bits->sfp (-> Integer Signature SFixedPoint))
(define (bits->sfp bits sig)
  (cond
    [(valid-range? sig #t bits) (SFixedPoint sig bits)]
    [else (error "not valid bits!")]))

(: get-fp-value (-> FixedPoint Exact-Rational))
(define (get-fp-value fp)
  (define dem (expt 2 (get-fb-bw (FixedPoint-sig fp))))
  (cond
    [(UFixedPoint? fp) (/ (UFixedPoint-bits fp) dem)]
    [(SFixedPoint? fp) (/ (SFixedPoint-bits fp) dem)]
    [else (error "typed racket makes me do so!")]))

(: get-fp-value-int (-> FixedPoint Integer))
(define (get-fp-value-int fp)
  (cond
    [(UFixedPoint? fp) (UFixedPoint-bits fp)]
    [(SFixedPoint? fp) (SFixedPoint-bits fp)]
    [else (error "typed racket makes me do so!")]))

;; rounding mode
;; round up
(struct RU ())
;; round down
(struct RD ())
(define-type RM (U RU RD))
(: RoundUp RU)
(define RoundUp (RU))
(: RoundDown RD)
(define RoundDown (RD))

;; overflow mode
;; saturate
(struct ST ())
;; wrap around
(struct WP ())
(define-type OM (U ST WP))
(: Saturate ST)
(define Saturate (ST))
(: WrapAround WP)
(define WrapAround (WP))

(: saturate (-> Signature Boolean Integer Integer))
(define (saturate sig sign val)
  (define tb (get-total-bw sig))
  (define max-val
    (- (expt 2 (if sign (- tb 1) tb)) 1))
  (define min-val
    (if sign (- (expt 2 (- tb 1))) 0))
  (cond
    [(> val max-val) max-val]
    [(< val min-val) min-val]
    [else val]))

(: wrap-around (-> Signature Boolean Integer Integer))
(define (wrap-around sig sign val)
  (define tb (get-total-bw sig))
  (cond
    [sign (let ([offset (expt 2 (- tb 1))])
            (- (modulo (+ val offset) (expt 2 tb)) offset))]
    [else (modulo val (expt 2 tb))]))

(: handle-overflow (-> OM Signature Boolean Integer Integer))
(define (handle-overflow om sig sign val)
  (cond
    [(ST? om) (saturate sig sign val)]
    [(WP? om) (wrap-around sig sign val)]))

(: handle-rounding (-> RM Signature Exact-Rational Integer))
(define (handle-rounding rm sig val)
  (define fb (get-fb-bw sig))
  (define bits-to-round (* val (expt 2 fb)))
  (cond
    [(RU? rm) (ceiling bits-to-round)]
    [(RD? rm) (floor bits-to-round)]))

(: binop (-> OM RM (-> Exact-Rational Exact-Rational Exact-Rational) FixedPoint FixedPoint FixedPoint))
(define (binop om rm op f1 f2)
  (define sig (FixedPoint-sig f1))
  (define sign (SFixedPoint? f1))
  (define v1 (get-fp-value f1))
  (define v2 (get-fp-value f2))
  (define res (op v1 v2))
  (define res-after-round (handle-rounding rm sig res))
  (define res-after-om (handle-overflow om sig sign res-after-round))
  (cond
    [(and (UFixedPoint? f1) (UFixedPoint? f2))
     (if (>= res-after-om 0)
         (UFixedPoint sig res-after-om)
         (error "something is messed up!"))]
    [(and (SFixedPoint? f2) (SFixedPoint? f2))
     (SFixedPoint sig res-after-om)]
    [else (error "type mismatch!")]))

(: fp+ (-> OM FixedPoint FixedPoint FixedPoint))
(define (fp+ om f1 f2)
  (binop om (RU) + f1 f2))

(: fp- (-> OM FixedPoint FixedPoint FixedPoint))
(define (fp- om f1 f2)
  (binop om (RU) - f1 f2))

(: fp* (-> OM RM FixedPoint FixedPoint FixedPoint))
(define (fp* om rm f1 f2)
  (binop om rm * f1 f2))

(: fp/ (-> OM RM FixedPoint FixedPoint FixedPoint))
(define (fp/ om rm f1 f2)
  (binop om rm / f1 f2))

(begin-for-syntax
  (define (format-op-names op-names)
    (map
     (λ (op-name)
       (format-id op-name "fp~a" op-name))
     (syntax->list op-names))))

(define-syntax (define-bin-rel stx)
  (syntax-case stx ()
    [(_ op-name ...)
     (with-syntax ([(op-name-q ...)
                    (format-op-names #'(op-name ...))])
       #`(begin
           (: op-name-q (-> FixedPoint FixedPoint Boolean)) ...
           (define (op-name-q f1 f2)
             (define v1 (get-fp-value f1))
             (define v2 (get-fp-value f2))
              (op-name v1 v2)) ...))]))

(define-bin-rel < <= > >= =)
