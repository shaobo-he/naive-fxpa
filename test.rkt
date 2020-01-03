#lang racket/base

(require "naive-fxpa.rkt")
(define header
  "from pysmt.shortcuts import SBV, Symbol, is_valid, Equals, Not

from pysmt.typing import UFXPType, SFXPType, FXP_OM, FXP_RM

from pysmt.shortcuts import (UFXPAdd, UFXPSub, UFXPMul, UFXPDiv,
                            SFXPAdd, SFXPSub, SFXPMul, SFXPDiv,
                            UFXP, SFXP, BV, ST, WP, RU, RD,
                            get_model, is_sat, UFXPLT, UFXPLE,
                            UFXPGT, UFXPGE, SFXPLT, SFXPLE,
                            SFXPGT, SFXPGE, Bool, Iff)

from pysmt.rewritings import get_fp_bv_converter

conv = get_fp_bv_converter()
")

(define (mk-test-fun op)
  (format "def test_fxp_~a():" op))

(define (lb sign bw)
  (cond
    [(= sign 0) 0]
    [else (- (expt 2 (- bw 1)))]))
   

(define (ub sign bw)
  (cond
    [(= sign 0) (expt 2 bw)]
    [else (expt 2 (- bw 1))]))

(define (format-constant f)
  (let ([tb (get-total-bits f)]
        [fb (get-frac-bits f)]
        [sign (get-fp-sign f)]
        [v (get-fp-value-int f)])
    (format "~aFXP(~a(~a, ~a), ~a)"
            (if sign "S" "U")
            (if sign "SBV" "BV")
            v tb fb)))

(define (rfp+ OM RM a b)
  (fp+ OM a b))
(define (rfp- OM RM a b)
  (fp- OM a b))
(define (rfp* OM RM a b)
  (fp* OM RM a b))
(define (rfp/ OM RM a b)
  (if (= (get-fp-value-int b) 0)
      (let* ([sign (get-fp-sign b)]
             [con (if sign bits->sfp bits->ufp)]
             [all-ones (if sign -1 (- (expt 2 (get-total-bits b)) 1))])
           (con all-ones (make-signature (get-total-bits b) (get-frac-bits b))))
      (fp/ OM RM a b)))
(define (rfp< OM RM a b)
  (fp< a b))
(define (rfp<= OM RM a b)
  (fp<= a b))
(define (rfp> OM RM a b)
  (fp> a b))
(define (rfp>= OM RM a b)
  (fp>= a b))

(define (f+ OM RM a b)
  (let ([fa (format-constant a)]
        [fb (format-constant b)]
        [sign (get-fp-sign a)])
    (format "~aFXPAdd(~a, ~a, ~a)"
            (if sign "S" "U")
            (if (ST? OM) "ST" "WP")
            fa fb)))

(define (f- OM RM a b)
  (let ([fa (format-constant a)]
        [fb (format-constant b)]
        [sign (get-fp-sign a)])
    (format "~aFXPSub(~a, ~a, ~a)"
            (if sign "S" "U")
            (if (ST? OM) "ST" "WP")
            fa fb)))

(define (f* OM RM a b)
  (let ([fa (format-constant a)]
        [fb (format-constant b)]
        [sign (get-fp-sign a)])
    (format "~aFXPMul(~a, ~a, ~a, ~a)"
            (if sign "S" "U")
            (if (ST? OM) "ST" "WP")
            (if (RU? RM) "RU" "RD")
            fa fb)))

(define (f/ OM RM a b)
  (let ([fa (format-constant a)]
        [fb (format-constant b)]
        [sign (get-fp-sign a)])
    (format "~aFXPDiv(~a, ~a, ~a, ~a)"
            (if sign "S" "U")
            (if (ST? OM) "ST" "WP")
            (if (RU? RM) "RU" "RD")
            fa fb)))

(define (f< OM RM a b)
    (let ([fa (format-constant a)]
        [fb (format-constant b)]
        [sign (get-fp-sign a)])
    (format "~aFXPLT(~a, ~a)"
            (if sign "S" "U")
            fa fb)))

(define (f<= OM RM a b)
    (let ([fa (format-constant a)]
        [fb (format-constant b)]
        [sign (get-fp-sign a)])
    (format "~aFXPLE(~a, ~a)"
            (if sign "S" "U")
            fa fb)))

(define (f> OM RM a b)
    (let ([fa (format-constant a)]
        [fb (format-constant b)]
        [sign (get-fp-sign a)])
    (format "~aFXPGT(~a, ~a)"
            (if sign "S" "U")
            fa fb)))

(define (f>= OM RM a b)
    (let ([fa (format-constant a)]
        [fb (format-constant b)]
        [sign (get-fp-sign a)])
    (format "~aFXPGE(~a, ~a)"
            (if sign "S" "U")
            fa fb)))

(define (fexp ops OM RM a b)
  (let ([exp ((car ops) OM RM a b)])
    (format
     "  assert(is_sat(conv.convert(~a(~a, ~a))))"
     (if (FixedPoint? exp) "Equals" "Iff")
     ((cdr ops) OM RM a b)
     (cond
       [(FixedPoint? exp) (format-constant exp)]
       [else (if exp "Bool(True)" "Bool(False)")]))))

(define (get-test op)
  (let* ([s (random 0 2)]
         [bw (random 3 32)]
         [fw (random 1 (+ 1 bw))]
         [lb (lb s bw)]
         [ub (ub s bw)]
         [n1 (random lb ub)]
         [n2 (random lb ub)]
         [con (cond [(= s 0) bits->ufp] [else bits->sfp])]
         [om (list-ref `(,(ST) ,(WP)) (random 0 2))]
         [rm (list-ref `(,(RU) ,(RD)) (random 0 2))]
         [a (con n1 (make-signature bw fw))]
         [b (con n2 (make-signature bw fw))])
    (fexp op om rm a b)))

(define ops
  `(,(cons "add" (cons rfp+ f+))
    ,(cons "sub" (cons rfp- f-))
    ,(cons "mul" (cons rfp* f*))
    ,(cons "div" (cons rfp/ f/))
    ,(cons "lt" (cons rfp< f<))
    ,(cons "le" (cons rfp<= f<=))
    ,(cons "gt" (cons rfp> f>))
    ,(cons "ge" (cons rfp>= f>=)))
  )

(begin
  (display header)
  (for ([j (in-range (length ops))])
    (let ([op (cdr (list-ref ops j))]
          [name (car (list-ref ops j))])
      (begin
        (displayln (mk-test-fun name))
        (for ([i (in-range 5000)])
          (displayln (get-test op))
          )
        (displayln (format "test_fxp_~a()" name))))))