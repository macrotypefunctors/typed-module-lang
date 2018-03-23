#lang s-exp typed-module-lang/mod-lang
(mod
 (type Op2 = (-> Int Int Int))
 (val x : Int = 5)
 (val y : Int = x))
