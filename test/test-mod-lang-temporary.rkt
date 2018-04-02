#lang s-exp typed-module-lang/mod-lang
(define-module M =
  (mod
   (type Op2 = (-> Nit Int Nit))
   (type Nit = Int)
   (val x : Int = 5)
   (val y : Int = x)))
