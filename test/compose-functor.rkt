#lang typed-module-lang

(define-signature TRANS =
  (sig (type In)
       (type Out)
       (val f : (-> In Out))))

(define-module Thrush =
  (λ ([A : TRANS])
    (λ ([B : (where TRANS In = A.Out)])
      (mod
       (type In = A.In)
       (type Out = B.Out)
       (val f : (-> In Out) =
            (λ (x) (B.f (A.f x))))))))

(define-module Even =
  (mod (type In = Int)
       (type Out = Bool)
       (val f : (-> In Out) = (λ (x) (= (rem x 2) 0)))))

(define-module Lambool =
  (mod (type In = Bool)
       (type Out = (-> Int Int Int))
       (val f : (-> In Out) = (λ (b) (λ (t f) (if b t f))))))

(define-module EvenLambool = ((Thrush Even) Lambool))
