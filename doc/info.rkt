#lang info

;; ---------------------------------------------------------

;; Package Info

(define collection "typed-module-lang-doc")

(define deps
  '("base"
    "typed-module-lang-lib"
    "scribble-lib"
    ))

(define build-deps
  '("racket-doc"
    ))

;; ---------------------------------------------------------

;; Collection Info

(define scribblings
  '(["typed-module-lang.scrbl" ()]))

;; ---------------------------------------------------------

