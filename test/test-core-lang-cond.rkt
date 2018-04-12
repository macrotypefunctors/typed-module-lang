#lang s-exp typed-module-lang/core-lang

(type Nat = Int)
(type NatPair = Int)

(val fst : (-> NatPair Nat) =
  (λ (x)
    (if (= (rem x 2) 0)
        (+ 1 (fst (quo x 2)))
        0)))

(val snd : (-> NatPair Nat) =
  (λ (x)
    (if (= (rem x 3) 0)
        (+ 1 (snd (quo x 3)))
        0)))

(val pair : (-> Nat Nat NatPair) =
  (λ (x y)
    (if (= x 0)
        (if (= y 0)
            1
            (* 3 (pair 0 (- y 1))))
        (* 2 (pair (- x 1) y)))))

(val p1 : NatPair = (pair 5 2))
(check p1 = 288) ; = 2^5 * 3^2

(val p2 : NatPair = (pair 7 11))
(check (fst p2) = 7)
(check (snd p2) = 11)
