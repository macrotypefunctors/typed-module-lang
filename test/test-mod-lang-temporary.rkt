#lang s-exp typed-module-lang/mod-lang

(define-signature S =
  (sig (type Nit)
       (type Op2 = (-> Nit Nit Nit))
       (val x : Nit)
       (val three : Int)
       (val four : Nit)))

(define-module M =
  (seal
   (mod
    (type Op2 = (-> Nit Int Nit))
    (type Nit = Int)

    (val x : Int = 5)
    (val z : Nit = x)
    (val three : Int = (+ 1 2))

    (val add : Op2 = +)
    (val four : Int = (add 2 2))

    ;(val not-op2 : Op2 = 3)
    ;(val bad-app : Int = (3 4))
    )
   :>
   S))
