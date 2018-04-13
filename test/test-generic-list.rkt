#lang typed-module-lang

(define-signature LIST =
  (sig (type T)
       (type E)
       (val empty : T)
       (val cons : (-> E T T))
       (val empty? : (-> T Bool))
       (val first : (-> T E))
       (val rest : (-> T T))))

(define-signature ELEM =
  (sig (type T)
       (val ->int : (-> T Int))
       (val int-> : (-> Int T))))

(define-module PrimeExpt =
  (λ ([Elem : ELEM])
    (mod (type T = Int)
         (type E = Elem.T)
         (val empty : T = 0)
         
         (val cons* : (-> Int T T) =
              (λ (x y)
                (if (= x 0)
                    (if (= y 0) 1
                        (* 2 (cons* x (- y 1))))
                    (* 3 (cons* (- x 1) y)))))

         (val cons : (-> E T T) =
              (λ (x y)
                (cons* (Elem.->int x) y)))
         
         (val empty? : (-> T Bool) =
              (λ (n) (= n 0)))
         
         (val first* : (-> T Int) =
              (λ (n) (if (= (rem n 3) 0)
                         (+ 1 (first* (quo n 3)))
                         0)))

         (val first : (-> T E) =
              (λ (n) (Elem.int-> (first* n))))
         
         (val rest : (-> T T) =
              (λ (n) (if (= (rem n 2) 0)
                         (+ 1 (rest (quo n 2)))
                         0))))))

(define-module PrimeExpt* =
  (seal PrimeExpt :> (Π ([E : ELEM]) (where LIST E = E.T))))

