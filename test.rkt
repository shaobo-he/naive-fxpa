#lang racket/base

(require "naive-fxpa.rkt")
(define header
  "from pysmt.shortcuts import SBV, Symbol, is_valid, Equals, Not

from pysmt.typing import UFXPType, SFXPType, FXP_OM, FXP_RM

from pysmt.shortcuts import (UFXPAdd, UFXPSub, UFXPMul, UFXPDiv,
                            SFXPAdd, SFXPSub, SFXPMul, SFXPDiv,
                            UFXP, SFXP, BV, ST, WP, RU, RD,
                            get_model, is_sat)

from pysmt.rewritings import get_fp_bv_converter

conv = get_fp_bv_converter()
")
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

(define (fexp ops OM RM a b)
  (format
   "assert(is_sat(conv.convert(Equals(~a, ~a))))"
   ((cdr ops) OM RM a b)
   (format-constant ((car ops) OM RM a b))))

(define (get-test)
  (let* ([s (random 0 2)]
         ;[bw (random 3 17)]
         ;[fw (random 0 (+ 1 bw))]
         [bw 16]
         [fw 8]
         [lb (lb s bw)]
         [ub (ub s bw)]
         [n1 (random lb ub)]
         [n2 (random lb ub)]
         [con (cond [(= s 0) bits->ufp] [else bits->sfp])]
         [op (list-ref `(,(cons rfp+ f+) ,(cons rfp- f-) ,(cons rfp* f*)) (random 0 3))]
         [om (list-ref `(,(ST) ,(WP)) (random 0 2))]
         [rm (list-ref `(,(RU) ,(RD)) (random 0 2))]
         [a (con n1 (make-signature bw fw))]
         [b (con n2 (make-signature bw fw))])
    (fexp op om rm a b)))

(begin
  (display header)
(for ([i (in-range 100)])
  (displayln (get-test))
  ))