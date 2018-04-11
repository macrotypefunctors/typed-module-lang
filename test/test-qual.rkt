#lang typed-module-lang

(define-module N =
  (seal
   (mod (type C = Int))
   :>
   (sig (type C))))

(define-module M =
  (mod
   (type A = Int)
   (type T1 = A)
   (type T3 = N.C)))

(define-module M/1 =
  (seal M
        :>
        (sig (type A = M.A)
             (type T1 = M.T1)
             (type T3 = M.T3))))

(define-module M/2 =
  (seal M
        :>
        (sig (type A = Int)
             (type T1 = M.A)
             (type T3 = N.C))))

