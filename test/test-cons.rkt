#lang typed-module-lang

(define-signature LIST =
  (sig (type T)
       (val empty : T)
       (val cons : (-> Int T T))
       (val empty? : (-> T Bool))
       (val first : (-> T Int))
       (val rest : (-> T T))))

(define-module TestPair =
  (λ ([L : LIST])
    (mod (val list1 : L.T = (L.cons 2 L.empty))
         (val list2 : L.T = (L.cons 1 list1))
         (check (L.empty? L.empty) = #t)
         (check (L.empty? list1) = #f)
         (check (L.first list1) = 2)
         (check (L.rest list2) = list1))))

(define-module PrimeExpt =
  (seal
   (mod (type T = Int)
        (val empty : T = 0)
        (val cons : (-> Int T T) =
          (λ (x y)
            (if (= x 0)
                (if (= y 0) 1
                    (* 2 (cons x (- y 1))))
                (* 3 (cons (- x 1) y)))))

        (val empty? : (-> T Bool) =
          (λ (n) (= n 0)))

        (val first : (-> T Int) =
          (λ (n) (if (= (rem n 3) 0)
                     (+ 1 (first (quo n 3)))
                     0)))

        (val rest : (-> T Int) =
          (λ (n) (if (= (rem n 2) 0)
                     (+ 1 (rest (quo n 2)))
                     0))))
   :> LIST))

(define-module TestPrimeExpt = (TestPair PrimeExpt))
