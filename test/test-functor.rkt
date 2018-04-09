#lang typed-module-lang

(define-signature S =
  (sig (type X)
       (val x : X)))

(define-module F =
  (λ ([a : S])
    (mod
     (type Y = Int)
     (val y : Y = 5))))

(define-module F* =
  (seal F :> (Π ([a : S]) (sig (type Y) (val y : Y)))))

