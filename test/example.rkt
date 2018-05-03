#lang typed-module-lang

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
  (sig
   (type Bool)
   (type Nat)
   (val z : Nat)
   (val z? : (-> Nat Bool))
   (val add1 : (-> Nat Nat))
   ;; sub1 raises an error if its argument is z
   (val sub1 : (-> Nat Nat))))

(define-signature NAT =
  (Π ([B : BOOL-REP])
    (Π ([N : (where NAT-REP Bool = B.Bool)])
      (sig
       ;; equality
       (val = : (-> N.Nat N.Nat B.Bool))
     
       ;; arithmetic
       (val + : (-> N.Nat N.Nat N.Nat))))))

(define-module Bool-Rep =
  (seal
   (mod
    (type Bool = (∀ (X) (-> (-> X) (-> X) X)))
    (val true : Bool = (Λ (X) (λ (t f) (t))))
    (val false : Bool = (Λ (X) (λ (t f) (f))))
    (val if : (∀ (X) (-> Bool (-> X) (-> X) X)) =
         (Λ (X) (λ (b t f) ((inst b X) t f)))))
   :>
   BOOL-REP))

(define-module Nat =
  (seal
   (λ ([B : BOOL-REP])
     (λ ([N : (where NAT-REP Bool = B.Bool)])
       (mod
        ;; comparison
        (val = : (-> N.Nat N.Nat B.Bool) =
             (λ ([a : N.Nat] [b : N.Nat])
               ((inst B.if B.Bool)
                (N.z? a)
                (λ () (N.z? b))
                (λ () ((inst B.if B.Bool) (N.z? b)
                                          (λ () B.false)
                                          (λ () (= (N.sub1 a) (N.sub1 b))))))))
        ;; arithmetic
        (val + : (-> N.Nat N.Nat N.Nat) =
             (λ ([a : N.Nat] [b : N.Nat])
               ((inst B.if N.Nat) (N.z? a)
                                  (λ () b)
                                  (λ () (N.add1 (+ (N.sub1 a) b)))))))))
   :>
   NAT))

(define-module Nat-Rep/Int =
  (seal
   (mod (type Bool = Bool-Rep.Bool)
        (type Nat = Int)
        (val z : Nat = 0)
        (val z? : (-> Nat Bool) = (λ (x) (if (= x 0) Bool-Rep.true Bool-Rep.false)))
        (val add1 : (-> Nat Nat) = (λ (x) (+ x 1)))
        ;; sub1 raises an error if its argument is z
        (val sub1 : (-> Nat Nat) = (λ (x) (- x 1))))
   :>
   (where NAT-REP Bool = Bool-Rep.Bool)))
    
(define-module Nat/Int =
  ((Nat Bool-Rep) Nat-Rep/Int))

(define-module TestNat =
  (λ ([NR : (where NAT-REP Bool = Bool-Rep.Bool)])
    (mod
     (define-module N = ((Nat Bool-Rep) NR))
     (type Bool = Bool-Rep.Bool)
     (type Nat = NR.Nat)
     (val true : Bool = Bool-Rep.true)
     (val false : Bool = Bool-Rep.false)
     (val n0 : Nat = NR.z)
     (val n1 : Nat = (NR.add1 n0))
     (val n2 : Nat = (NR.add1 n1))
     (val n3 : Nat = (NR.add1 n2))
     (val n4 : Nat = (NR.add1 n3))
     (val n5 : Nat = (NR.add1 n4))
     (val n6 : Nat = (NR.add1 n5))
     (val n7 : Nat = (NR.add1 n6))
     (val n8 : Nat = (NR.add1 n7))
     (val n9 : Nat = (NR.add1 n8))

     (check (N.= (N.+ n3 n5) n8) = Bool-Rep.true))))

(define-module TestNat/Int =
  (TestNat Nat-Rep/Int))

