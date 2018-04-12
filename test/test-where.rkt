#lang typed-module-lang

(define-signature A = (sig (type X) (val x : X) (val f : (-> X Int))))
(define-signature B = (sig (type X) (type Y) (val y : Y) (val f : (-> Y X))))
(define-signature C = (sig (type X) (val f-y : X)))

(define-module A* =
  (seal (mod (type X = Int)
             (val x : X = 5)
             (val f : (-> X Int) = (λ (x) x)))
        :>
        A))

(define-module B*/A =
  (λ ([A* : A])
    (seal
     (mod (type X = A*.X)
          (type Y = (-> X))
          (val y : Y = (λ () A*.x))
          (val f : (-> Y X) = (λ (y) (y))))
     :>
     (where B X = A*.X))))

(define-module C*/AB =
  (λ ([A* : A])
    (λ ([B* : (where B Y = A*.X)])
      (seal
       (mod (type X = A*.X)
            (val ffy : X = (A*.f (B*.f B*.y))))
       :>
       (where C X = A*.X)))))

