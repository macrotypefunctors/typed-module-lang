#lang typed-module-lang

(define-signature RING =
  (sig (type T)
       (val zero : T)
       (val one : T)
       (val add : (-> T T T))
       (val mul : (-> T T T))))

(define-signature EXAMPLES =
  (sig (type T)
       (val x : T)
       (val y : T)
       (val z : T)))

(define-module TestRingOps =
  (λ ([R : RING])
    (λ ([Eg : (where EXAMPLES T = R.T)])
      (mod
       ; + identity
       (check (R.add Eg.x R.zero) = Eg.x)
       ; + assoc
       (check (R.add Eg.x (R.add Eg.y Eg.z)) =
              (R.add (R.add Eg.x Eg.y) Eg.z))

       ; * zero
       (check (R.mul Eg.x R.zero) = R.zero)
       ; * identity
       (check (R.mul Eg.x R.one) = Eg.x)
       ; * assoc
       (check (R.mul Eg.x (R.mul Eg.y Eg.z)) =
              (R.mul (R.mul Eg.x Eg.y) Eg.z))

       ; *+ distr
       (check (R.mul Eg.x (R.add Eg.y Eg.z)) =
              (R.add (R.mul Eg.x Eg.y)
                     (R.mul Eg.x Eg.z)))))))

(define-module IntRing =
  (mod (type T = Int)
       (val zero : T = 0)
       (val one : T = 1)
       (val add : (-> T T T) = +)
       (val mul : (-> T T T) = *)))

(define-module IntEg =
  (mod (type T = Int)
       (val x : T = 123)
       (val y : T = -89)
       (val z : T = 1077)))

(define-module TestIntRing = ((TestRingOps IntRing) IntEg))

;; ----------------------------------------

(define-module BoolRing =
  (mod (type T = Bool)
       (val zero : T = #f)
       (val one : T = #t)
       (val add : (-> T T T) = (λ (x y) (if x one y)))
       (val mul : (-> T T T) = (λ (x y) (if x y zero)))))

(define-module BoolEg1 =
  (mod (type T = Bool)
       (val x : T = #t) (val y : T = #f) (val z : T = #t)))

(define-module BoolEg2 =
  (mod (type T = Bool)
       (val x : T = #f) (val y : T = #t) (val z : T = #f)))

(define-module TestBoolRing1 = ((TestRingOps BoolRing) BoolEg1))
(define-module TestBoolRing2 = ((TestRingOps BoolRing) BoolEg2))
