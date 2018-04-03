#lang s-exp typed-module-lang/core-lang

(type Op2 = (-> Nit Int Nit))
(type Nit = Int)

(val x : Int = 5)
(val z : Nit = x)
(val plus : Op2 = +)
;(val bad : Int = (plus 1 2))
