#lang racket/base
(require racket/match racket/bool racket/dict syntax/id-table
         (only-in cond-strict [cond/strict cond]))

;; ---------------------------------------------------------

;; A Signature is one of:
;;  - Sig
;;  - PiSig

;; ---------------------------------------------------------

;; A ModExpr is one of:
;;  - Id

;; ---------------------------------------------------------

;; A Sig is represented with a
;;   (Hashof Symbol SigComponent)

;; A SigComponent is one of:
;;  - (type-alias-decl [TypeWOpaque Symbol])
;;  - (type-opaque-decl)
;;  - (val-decl Type)

(struct type-alias-decl [type] #:prefab)
(struct type-opaque-decl [] #:prefab)
(struct val-decl [type] #:prefab)

;; ---------------------------------------------------------

;; A PiSig is represented with a
;;   (pi-sig Id Signature Signature)

;; The id `x` is a binding position with the scope of `out`
(struct pi-sig [x in out] #:prefab)

;; ---------------------------------------------------------

;; A [TypeWOpaque X] is one of:
;;  - BaseType
;;  - (-> [TypeWOpaque X] [TypeWOpaque X])
;;  - (opaque-type-reference X)
;;  - (dot ModExpr Symbol)
;;  - TODO: ∀

(struct Int [] #:prefab)
(struct opaque-type-reference [X] #:prefab)
(struct dot [mod type-name] #:prefab)

;; ---------------------------------------------------------

;; A MEnv is a [IdTable Signature]
;; representing module-level variables

;; MEnv MEnv Signature Signature -> Bool
(define (signature-matches? m-env1 m-env2 A B)
  (cond
    [(and (hash? A) (hash? B))     (sig-matches? m-env1 m-env2 A B)]
    [(and (pi-sig? A) (pi-sig? B)) (pi-sig-matches? m-env1 m-env2 A B)]))

;; MEnv MEnv PiSig PiSig -> Bool
(define (pi-sig-matches? m-env1 m-env2 A B)
  (match-define (pi-sig A-x A-in A-out) A)
  (match-define (pi-sig B-x B-in B-out) B)
  (define B-out* (signature-subst B-out B-x A-x))
  (and
   (signature-matches? m-env1 m-env2
                       B-in A-in)
   ;; TODO: think about this `B-in` more, I think this corresponds to
   ;; the A' on page 8 of `Subtyping Dependent Types` by Aspinall +
   ;; Compagnoni 2000                       ||||
   ;;                                       vvvv
   (signature-matches? (dict-set m-env1 A-x B-in)
                       (dict-set m-env2 A-x B-in)
                       A-out B-out*)))

(define (signature-subst S x y)
  (unless (free-identifier=? x y)
    (error "TODO. identifiers not equal"))
  S)

;; ---------------------------------------------------------

;; An OTyEnv is a [Hashof Symbol Type]
;; representing a mapping from opaque type names to 
;; definitions

;; MEnv MEnv Sig Sig -> Bool
(define (sig-matches? m-env1 m-env2 A B)
  ;; process type declarations first
  ;; get the mapping from B's opaque types to A's types
  (define b->a
    (for/fold ([b->a (hash)])
              ([(sym B-comp) (in-hash B)]
               #:when (type-opaque-decl? B-comp))
      #:break (not b->a)
      (let ([A-comp (hash-ref A sym #f)])
        (match A-comp
          [(type-alias-decl t)
           (hash-set b->a sym t)]
          [(type-opaque-decl)
           (hash-set b->a sym (opaque-type-reference sym))]
          [_
           #false]))))

  ;; create an identity mapping for A's opaque types
  (define a->a
    (for/hash ([(sym A-comp) (in-hash A)]
               #:when (type-opaque-decl? A-comp))
      (values sym (opaque-type-reference sym))))

  (and b->a
       (for/and ([(sym B-comp) (in-hash B)])
         (let ([A-comp (hash-ref A sym #f)])
           (and A-comp
                (sig-component-matches? m-env1 m-env2 a->a b->a
                                        A-comp B-comp))))))

;; MEnv MEnv OTyEnv OTyEnv SigComp SigComp -> Boolean
(define (sig-component-matches? m-env1 m-env2 A-env B-env A B)
  (match* [A B]
    [[(val-decl A) (val-decl B)]
     (type-matches? m-env1 m-env2 A-env B-env A B)]
    [[(type-alias-decl A) (type-alias-decl B)]
     (type-equal? m-env1 m-env2 A-env B-env A B)]
    [[(type-opaque-decl) (type-opaque-decl)]
     #true]
    [[(type-alias-decl _) (type-opaque-decl)]
     #true]
    [[_ _]
     #false]))

;; MEnv MEnv OTyEnv OTyEnv Type Type -> Boolean
(define (type-equal? m-env1 m-env2 A-env B-env A B)
  (and (type-matches? m-env1 m-env2 A-env B-env A B)
       (type-matches? m-env2 m-env1 B-env A-env B A)))

;; MEnv MEnv OTyEnv OTyEnv Type Type -> Boolean
(define (type-matches? m-env1 m-env2 A-env B-env A B)
  (match* [A B]
    [[_ _] #:when (equal? A B) #t]

    ;; TODO: function type

    [[(opaque-type-reference x) _]
     #:when A-env
     (type-matches? m-env1 m-env2 #f B-env (hash-ref A-env x) B)]

    [[_ (opaque-type-reference y)]
     #:when B-env
     (type-matches? m-env1 m-env2 A-env #f A (hash-ref B-env y))]

    [[(opaque-type-reference x) (opaque-type-reference y)]
     (symbol=? x y)]

    [[(dot m x) _]
     #:when m-env1
     (type-matches? #f m-env2 A-env B-env
                    (lookup-mod-type m-env1 m x)
                    B)]
    [[_ (dot m y)]
     #:when m-env2
     (type-matches? m-env1 #f A-env B-env
                    A
                    (lookup-mod-type m-env2 m y))]

    [[_ _]
     #false]))

;; -----------------------------------------------------

;; lookup-mod-type : MEnv ModExpr Sym -> Type
(define (lookup-mod-type m-env m x)
  (unless (identifier? m)
    (error "TODO: m is not an id"))
  (unless (dict-has-key? m-env m)
    (error "m is not defined"))
  (define m-sig (dict-ref m-env m))
  (unless (hash? m-sig)
    (error "m is not a `mod`"))
  (unless (hash-has-key? m-sig x)
    (error "sig does not have x"))
  (match (hash-ref m-sig x)
    [(type-opaque-decl)
     ;; TODO: make sure this isn't an infinite loop
     (dot m x)]
    [(type-alias-decl t)
     (qualify-opaque-references t m)]
    [_
     (error "not a type declaration")]))

;; qualify-opaque-references : Type ModExpr -> Type
(define (qualify-opaque-references t m)
  (match t
    [(opaque-type-reference sym)
     (dot m sym)]
    [(Int) t]))

;; -----------------------------------------------------

(module+ test
  (require rackunit racket/function)
  (define-binary-check (check-sig-matches A B)
    (signature-matches? (hash) (hash) A B))
  (define-binary-check (check-not-sig-matches A B)
    (not (signature-matches? (hash) (hash) A B)))

  (define sig hash)

  (define empty (hash))
  (define sig-X=int
    (sig
     'X (type-alias-decl (Int))))
  (define sig-X-opaque
    (sig
     'X (type-opaque-decl)))

  (check-sig-matches empty empty)
  (check-sig-matches sig-X=int sig-X=int)
  (check-sig-matches sig-X-opaque sig-X-opaque)

  (check-sig-matches sig-X=int sig-X-opaque)
  (check-not-sig-matches sig-X-opaque sig-X=int)


  (define sig-X/Y-x:X
    (sig
     'X (type-opaque-decl)
     'Y (type-alias-decl (opaque-type-reference 'X))
     'x (val-decl (opaque-type-reference 'X))))

  (define sig-X/Y-x:Y
    (sig
     'X (type-opaque-decl)
     'Y (type-opaque-decl)
     'x (val-decl (opaque-type-reference 'Y))))

  (check-sig-matches sig-X/Y-x:X sig-X/Y-x:Y)
  (check-not-sig-matches sig-X/Y-x:Y sig-X/Y-x:X)


  (define sig-X-Y=X
    (sig
     'X (type-opaque-decl)
     'Y (type-alias-decl (opaque-type-reference 'X))))

  (define sig-Y-X=Y
    (sig
     'Y (type-opaque-decl)
     'X (type-alias-decl (opaque-type-reference 'Y))))

  (check-not-sig-matches sig-X-Y=X sig-Y-X=Y)


  (check-sig-matches
   (sig 'v (val-decl (Int))
        'X (type-alias-decl (Int))
        'Y (type-alias-decl (Int)))
   (sig 'v (val-decl (opaque-type-reference 'X))
        'X (type-opaque-decl)
        'Y (type-alias-decl (opaque-type-reference 'X))))

  (check-sig-matches
   (sig 'X (type-opaque-decl)
        'Y (type-alias-decl (opaque-type-reference 'X)))
   (sig 'Y (type-opaque-decl)))

  (let ([x #'x]
        [I  (sig 't (type-opaque-decl))]
        [I* (sig 't (type-alias-decl (Int)))]
        [J  (sig 's (type-opaque-decl) 't (type-opaque-decl))]
        [J* (sig 's (type-opaque-decl) 't (type-alias-decl (opaque-type-reference 's)))])
    (check-sig-matches I* I)
    (check-sig-matches J* J)

    (check-sig-matches
     (pi-sig x I (sig 'v (val-decl (dot x 't))))
     (pi-sig x I* (sig 'v (val-decl (dot x 't)))))

    (check-sig-matches
     (pi-sig x I (sig 'v (val-decl (dot x 't))))
     (pi-sig x I* (sig 'v (val-decl (Int)))))

    (check-sig-matches
     (pi-sig x J (sig 'v (val-decl (dot x 't))))
     (pi-sig x J* (sig 'v (val-decl (dot x 't)))))

    (check-sig-matches
     (pi-sig x J (sig 'v (val-decl (dot x 't))))
     (pi-sig x J* (sig 'v (val-decl (dot x 's)))))

    (check-not-sig-matches
     (pi-sig x J (sig 'v (val-decl (dot x 't))))
     (pi-sig x J* (sig 'v (val-decl (Int)))))
    )
  )
