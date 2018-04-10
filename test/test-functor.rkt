#lang typed-module-lang

(define-signature S =
  (sig (type X)
       (val x : X)))

(define-module F =
  (λ ([A : S])
    (mod
     (type Y = Int)
     (val y : Y = 5))))

(define-module F* =
  (seal F :> (Π ([A : S]) (sig (type Y) (val y : Y)))))

;; ------------

(define-module A =
  (mod
   (type X = Int)
   (val x : X = 5)))

(define-module F<-A =
  (F A))

(define-module F*<-A =
  (F* A))
