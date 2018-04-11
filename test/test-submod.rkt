#lang typed-module-lang

(define-module M =
  (mod
   (define-module Inner =
     (mod
      (type T = Int)))))

(define-module Test =
  (seal (mod (val x : Int = 3))
        :>
        (sig (val x : M.Inner.T))))
