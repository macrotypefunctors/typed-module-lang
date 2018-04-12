#lang typed-module-lang

(define-signature PAIR =
  (sig (type T)
       (val cons : (-> Int Int T))
       (val car : (-> T Int))
       (val cdr : (-> T Int))))

(define-module TestPair =
  (λ ([P : PAIR])
    (mod (val p1 : P.T = (P.cons 7 11))
         (val p2 : P.T = (P.cons 15 4))
         (check (P.car p1) = 7)
         (check (P.cdr p1) = 11)
         (check (P.car p2) = 15)
         (check (P.cdr p2) = 4))))

(define-module PrimeExpt =
  (mod
   (type T = Int)
   (val car : (-> T Int) =
     (λ (x)
       (if (= (rem x 2) 0)
           (+ 1 (car (quo x 2)))
           0)))

   (val cdr : (-> T Int) =
     (λ (x)
       (if (= (rem x 3) 0)
           (+ 1 (cdr (quo x 3)))
           0)))

   (val cons : (-> Int Int T) =
     (λ (x y)
       (if (= x 0)
           (if (= y 0)
               1
               (* 3 (cons 0 (- y 1))))
           (* 2 (cons (- x 1) y)))))))

(define-module TestPrimeExpt = (TestPair PrimeExpt))
