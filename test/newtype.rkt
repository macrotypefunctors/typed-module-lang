#lang typed-module-lang

(define-module M =
  (mod
   (newtype X = (x Int))

   (check (x 5) = (x 5))))

(define-module M* =
  (seal M
        :>
        (sig (type X)
             (val x : (-> Int X)))))

