#lang s-exp typed-module-lang/core-lang

(type Op2 = (-> Int Int Int))

(val x : Int = 5)

(val y : Int = x)
