#lang s-exp typed-module-lang/mod-lang

(define-signature S =
  (sig
   (type T = Int)
   (val f : (-> T Int))))

(define-signature S* =
  (sig
   (type T)
   (val f : (-> T Int))))

(define-module M =
  (mod
   (type T = Int)
   (val f : (-> T Int) = (λ (x) 5))))

(define-module M* = (seal M :> S*))

(define-signature BOOL-REP =
  (sig
   (type Bool)
   (val true : Bool)
   (val false : Bool)
   (val if : (∀ (X) (-> Bool (-> X) (-> X) X)))))

(define-signature NAT-REP =
  (Π ([B : BOOL-REP])
    (sig
     (type Nat)
     (val z : Nat)
     (val z? : B.Bool)
     (val add1 : (-> Nat Nat))
     ;; sub1 raises an error if its argument is z
     (val sub1 : (-> Nat Nat)))))

(define-signature NAT =
  (Π ([B : BOOL-REP] [N : NAT-REP])
    (sig
     (define-module N = (N B))
     ;; equality
     (val = : (-> N.Nat N.Nat B.Bool))
     
     ;; arithmetic
     (val + : (-> N.Nat N.Nat N.Nat)))))

(define-module Bool-Rep =
  (seal
   (mod
    (type Bool = (∀ (X) (-> (-> X) (-> X) X)))
    (val true = (Λ (X) (λ (t f) (t))))
    (val false = (Λ (X) (λ (t f) (f))))
    (val if = (Λ (X) (λ (b t f) (b t f)))))
   :>
   BOOL-REP))

(define-module Nat =
  (seal
   (λ ([B : BOOL-REP] [N : NAT-REP])
     (mod
      (define-module N = (N B))
      ;; comparison
      (val = = (λ ([a : N.Nat] [b : N.Nat])
                 (B.if (N.z? a)
                       (λ () (N.z? b))
                       (λ () (B.if (N.z? b)
                                   (λ () B.false)
                                   (λ () (= (N.sub1 a) (N.sub1 b))))))))
      ;; arithmetic
      (val + = (λ ([a : N.Nat] [b : N.Nat])
                 (B.if (N.z? a)
                       (λ () b)
                       (λ () (N.add1 (+ (N.sub1 a) b))))))))
   :>
   NAT))

