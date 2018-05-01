#lang typed-module-lang

(define-module M =
  (mod
   (define-module Inner =
     (mod))))

(define-module M* =
  (seal M :> (sig)))

