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

(struct type-alias-decl [type] #:prefab)
(struct newtype-decl [id type]
  ; id is the identifier for the constructor
  ; type is the argument to the constructor
  ; NOTE: don't substitute for type during subtype relation
  ;       newtype =/= type alias !
  #:prefab)

;; a DeclKindEnv is a [Listof [List Id DeclKind]]
;;   - 'type
;;   - 'val

;; a Env is a [Listof [List Id EnvBinding]]
;; an EnvBinding is one of
;;   - (val-binding Type)
;;   - (type-binding TypeDecl)

(struct val-binding [type])
(struct type-binding [decl])

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

;; Env -> DeclKindEnv
;; if it encounters a kind of binding that isn't val/type,
;; then it passes it through
(define (env->decl-kind-env G)
  (for/list ([entry (in-list G)])
    (match entry
      [(list x (val-binding _)) (list x 'val)]
      [(list x (type-binding _)) (list x 'type)]
      [_ entry])))

;; ------------------------------------------------------

;; a Type is one of
;;   - BaseType
;;   - (Arrow [Listof Type] Type)
;;   - (named-reference Id)
;;   - TODO: ∀

(struct Int [] #:prefab)
(struct Bool [] #:prefab)
(struct Arrow [inputs output] #:prefab)
(struct named-reference [id] #:prefab)
;; TODO: think about named-reference more, symbol vs. identifier,
;;       and also whether it's the right thing to use in the
;;       type-def-var rule

(define (subtype? G τ1 τ2)
  (subtype?/recur G τ1 τ2 subtype?))

;; Env Type Type [Env Type Type -> Boolean] -> Boolean
(define (subtype?/recur G A B recur-subtype?)
  (match* [A B]
    [[(Arrow τa-ins τa-out) (Arrow τb-ins τb-out)]
     (define (<: a b) (recur-subtype? G a b))
     (and (andmap <: τb-ins τa-ins)
          (<: τa-out τb-out))]

    ;; two identical named-reference types are equal; this handles the case of
    ;; two opaque types as well as preemtively matching aliases that
    ;; are obviously the same. if they are not identical then try to
    ;; reduce them by looking up type aliases. if we determine that
    ;; one is an opaque type, then we can fail because the only way
    ;; two opaque types can be the same is if they are referred to by
    ;; the same name. thus they should have been accepted by the
    ;; initial check.
    [[(named-reference x) (named-reference y)]
     #:when (free-identifier=? x y)
     #t]
    ;; TODO: would it be nicer to create a match pattern to match
    ;;       named-references bound to type-alias-decls?
    [[(named-reference x) _]
     (=> cont)
     (match (env-lookup-type-decl G x)
       [(type-alias-decl A*) (recur-subtype? G A* B)]
       [_ (cont)])]
    [[_ (named-reference y)]
     (=> cont)
     (match (env-lookup-type-decl G y)
       [(type-alias-decl B*) (recur-subtype? G A B*)]
       [_ (cont)])]

    [[_ _] (equal? A B)]))

;; Env Type Type -> Boolean
(define (type=? τ1 τ2)
  (and (subtype? τ1 τ2)
       (subtype? τ2 τ1)))


;; ---------------------------------------------------------

;; type-named-reference-map : [X -> Y] [TypeWNamedRef X] -> [TypeWNamedRef Y]
(define (type-named-reference-map f τ)
  (type-transform-named-reference τ (compose named-reference f)))

;; type-transform-named-reference :
;; [TypeWNamedRef X]
;; [X -> [TypeWNamedRef Y]]
;; ->
;; [TypeWNamedRef Y]

;; (type-transform-named-reference τ named-reference) = τ

(define (type-transform-named-reference τ f)
  (type-transform-named-reference/recur τ f type-transform-named-reference))

(define (type-transform-named-reference/recur τ f recur-ttnr)
  (define (ttnr-f t)
    (recur-ttnr t f))
  (match τ
    [(named-reference x)
     (f x)]
    [(Arrow ins out)
     (Arrow (map ttnr-f ins)
            (ttnr-f out))]
    ;; TODO: how do we know whether τ contains a
    ;; named-reference or not?
    [_ τ]))
