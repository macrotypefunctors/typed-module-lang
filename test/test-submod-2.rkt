#lang typed-module-lang

(define-module N =
  (seal (mod (type C = Int))
        :>
        (sig (type C))))

(define-module M =
  (mod
   (type A = (-> Int))
   (define-module J =
     (seal (mod (type D = (-> (-> Int))))
           :>
           (sig (type D))))
   (define-module L =
     (seal (mod
            (type B = (-> (-> (-> Int))))
            ;(type T1 = A)
            (type T2 = B)
            (type T3 = N.C)
            (type T4 = J.D))
           :>
           (sig
            (type B)
            ;(type T1 = A)
            (type T2 = B)
            (type T3 = N.C)
            (type T4 = J.D))))))

#|
A must have M.
J must have M.
B must have M.L.
|#

(define-module M-L* =
  (seal M.L
        :>
        (sig (type B)
             ;(type T1 = M.A)
             (type T2 = B)
             (type T3 = N.C)
             (type T4 = M.J.D))))

