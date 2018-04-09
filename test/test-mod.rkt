#lang typed-module-lang

(define-module Math =
  (mod
   (type T = Int)
   (val add1 : (-> T T) = (λ (x) (+ x 1)))
   (val mul2 : (-> T T) = (λ (x) (* x 2)))))

(define-signature MATH =
  (sig
   (type T)
   (val add1 : (-> T T))
   (val mul2 : (-> T T))))

(define-module Math* = (seal Math :> MATH))
