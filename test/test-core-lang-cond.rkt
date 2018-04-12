#lang s-exp typed-module-lang/core-lang

(type Nat = Int)
(type NatPair = Int)

(val car : (-> NatPair Nat) =
  (λ (x)
    (if (= (rem x 2) 0)
        (+ 1 (car (quo x 2)))
        0)))

(val cdr : (-> NatPair Nat) =
  (λ (x)
    (if (= (rem x 3) 0)
        (+ 1 (cdr (quo x 3)))
        0)))

(val cons : (-> Nat Nat NatPair) =
  (λ (x y)
    (if (= x 0)
        (if (= y 0)
            1
            (* 3 (cons 0 (- y 1))))
        (* 2 (cons (- x 1) y)))))

(val p1 : NatPair = (cons 5 2))
(check p1 = 288) ; = 2^5 * 3^2

(val p2 : NatPair = (cons 7 11))
(check (car p2) = 7)
(check (cdr p2) = 11)
