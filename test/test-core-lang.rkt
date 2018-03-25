#lang s-exp typed-module-lang/core-lang

(type Op2 = (-> Nit Int Nit))
(type Nit = Int)

(val x : Int = 5)
;(val x : Nit = 5)
(val y : Int = Nit)
