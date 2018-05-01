#lang typed-module-lang

(define-module M =
  (mod
   (define-module Inner =
     (mod (val x : Int = 3)))))

(define-module M* =
  (seal M :> (sig)))

(define-module M** =
  (seal M :> (sig (module Inner : (sig)))))

(define-module M*** =
  (seal M :> (sig (module Inner : (sig (val x : Int))))))
