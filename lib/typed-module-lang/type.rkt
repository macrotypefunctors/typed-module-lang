#lang racket
(provide (all-defined-out))

;; TODO: yes the below definitions look exactly like the
;;  definitions in "sig.rkt"; we should modify "sig.rkt" to
;;  use these definitions instead and just add a few new
;;  definitions:
;;    opaque type declarations
;;    modules in envs
;;    #%dot types

;; a TypeDecl is one of
;;   - (type-alias-decl Type)
;;   - (newtype-decl Id Type)

(struct type-alias-decl [type])
(struct newtype-decl [id type]
  ; id is the identifier for the constructor
  ; type is the argument to the constructor
  ; NOTE: don't substitute for type during subtype relation
  ;       newtype =/= type alias !
  )

;; a DeclKindEnv is a [Listof [List Id DeclKind]]
;; a DeclKind is one of
;;   - 'type-alias
;;   - 'newtype

;; a Env is a [Listof [List Id EnvBinding]]
;; an EnvBinding is one of
;;   - (val-binding Type)
;;   - (type-binding TypeDefn)

(struct val-binding [type])
(struct type-binding [decl])

;; Env -> [Listof Id]
(define (env-val-names G)
  (filter-map (match-lambda
                [(list X (val-binding _)) X]
                [_ #f])
              G))

;; Env Id -> TypeDecl or #f
(define (env-lookup-type-decl G X)
  (match (assoc X G free-identifier=?)
    [(list _ (type-binding td)) td]
    [_ #f]))

;; Env Id -> Type or #f
(define (env-lookup-val G x)
  (match (assoc x G free-identifier=?)
    [(list _ (val-binding τ)) τ]
    [_ #f]))

;; ------------------------------------------------------

;; a Type is one of
;;   - BaseType
;;   - (Arrow [Listof Type] Type)
;;   - (named-reference Id)
;;   - TODO: ∀

(struct Int [] #:prefab)
(struct Arrow [inputs output] #:prefab)
(struct named-reference [id] #:prefab)
;; TODO: think about named-reference more, symbol vs. identifier,
;;       and also whether it's the right thing to use in the
;;       type-def-var rule


;; Env Type Type -> Boolean
(define/match (subtype? G τ1 τ2)
  [[_ (Arrow τ1-ins τ1-out) (Arrow τ2-ins τ2-out)]
   (define (<: a b) (subtype? G a b))
   (and (andmap <: τ2-ins τ1-ins)
        (<: τ1-out τ2-out))]

  [[_ (named-reference x) (named-reference y)]
   (or (free-identifier=? x y)
       (match* [(env-lookup-type-decl x)
                (env-lookup-type-decl y)]
         [[(type-alias-decl τ1*) _] (subtype? G τ1* τ2)]
         [[_ (type-alias-decl τ2*)] (subtype? G τ1 τ2*)]
         [[_ _] #f]))]

  [[_ _ _] (equal? τ1 τ2)])

;; Env Type Type -> Boolean
(define (type=? τ1 τ2)
  (and (subtype? τ1 τ2)
       (subtype? τ2 τ1)))

;; TODO: change implicit ⇐ rule to use subtype?
