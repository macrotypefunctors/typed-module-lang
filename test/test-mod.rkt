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

(define-module Example =
  (mod
   (val double : (-> Int Math.T) =
     Math.mul2)))

(define-module Example* =
  (mod
   (val double : (-> Math*.T Math*.T) =
     Math*.mul2)))

;; NOTE: Math.T and Math*.T are incompatible (intentional)

(define-module Test =
  (mod
   (check (Math.add1 4) = 5)
   (check (Math.mul2 4) = 8)))
