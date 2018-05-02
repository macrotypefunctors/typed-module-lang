#lang racket
(provide (all-defined-out))

(require "../env/label-env.rkt")

;; An Environment has two parts:
;;  * The BindingStore maps identifiers to unique "labels"
;;  * The LabelEnv maps the labels to values

;; An [LabelEnvof X] has the operations:
;;   label-env-lookup : [LabelEnvof X] Label -> X
;;   label-env-extend : [LabelEnvof X] [Listof [List Label X]] -> [LabelEnvof X]

;; --------------------------------------------------------------

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

;; a DeclKindEnv is a [Lenvof DeclKind]

;; a Lenv is a [Lenvof EnvBinding]
;; an EnvBinding is one of
;;   - (val-binding Type)
;;   - (type-binding TypeDecl)

(struct val-binding [type])
(struct type-binding [decl])

;; Lenv Label -> TypeDecl or #f
(define (lenv-lookup-type-decl G X)
  (match (label-env-lookup G X)
    [(type-binding td) td]
    [_ #f]))

;; Lenv Id -> Type or #f
(define (lenv-lookup-val G x)
  (match (label-env-lookup G x)
    [(val-binding τ) τ]
    [_ #f]))

;; ------------------------------------------------------

;; a Type is one of
;;   - BaseType
;;   - (Arrow [Listof Type] Type)
;;   - (label-reference Label)
;;   - TODO: ∀

(struct Int [] #:prefab)
(struct Bool [] #:prefab)
(struct Arrow [inputs output] #:prefab)
(struct label-reference [label] #:prefab)

(define (subtype? G τ1 τ2)
  (subtype?/recur G τ1 τ2 subtype?))

;; Env Type Type [Env Type Type -> Boolean] -> Boolean
(define (subtype?/recur G A B recur-subtype?)
  (match* [A B]
    [[(Arrow τa-ins τa-out) (Arrow τb-ins τb-out)]
     (define (<: a b) (recur-subtype? G a b))
     (and (andmap <: τb-ins τa-ins)
          (<: τa-out τb-out))]

    ;; two identical label-reference types are equal; this handles the case of
    ;; two opaque types as well as preemtively matching aliases that
    ;; are obviously the same. if they are not identical then try to
    ;; reduce them by looking up type aliases. if we determine that
    ;; one is an opaque type, then we can fail because the only way
    ;; two opaque types can be the same is if they are referred to by
    ;; the same name. thus they should have been accepted by the
    ;; initial check.
    [[(label-reference x) (label-reference y)]
     #:when (label=? x y)
     #t]
    ;; TODO: would it be nicer to create a match pattern to match
    ;;       named-references bound to type-alias-decls?
    [[(label-reference x) _]
     (=> cont)
     (match (lenv-lookup-type-decl G x)
       [(type-alias-decl A*) (recur-subtype? G A* B)]
       [_ (cont)])]
    [[_ (label-reference y)]
     (=> cont)
     (match (lenv-lookup-type-decl G y)
       [(type-alias-decl B*) (recur-subtype? G A B*)]
       [_ (cont)])]

    [[_ _] (equal? A B)]))

;; Env Type Type -> Boolean
(define (type=? G τ1 τ2)
  (and (subtype? G τ1 τ2)
       (subtype? G τ2 τ1)))


;; ---------------------------------------------------------

;; type-label-reference-map : [X -> Y] [TypeWLabelRef X] -> [TypeWLabelRef Y]
(define (type-label-reference-map f τ)
  (type-transform-label-reference τ (compose label-reference f)))

;; type-transform-label-reference :
;; [TypeWLabelRef X]
;; [X -> [TypeWLabelRef Y]]
;; ->
;; [TypeWLabelRef Y]

;; This equation holds:
;; (type-transform-label-reference τ label-reference) = τ

(define (type-transform-label-reference τ f)
  (type-transform-label-reference/recur τ f type-transform-label-reference))

(define (type-transform-label-reference/recur τ f recur-ttlr)
  (define (ttlr-f t)
    (recur-ttlr t f))
  (match τ
    [(label-reference x)
     (f x)]
    [(Arrow ins out)
     (Arrow (map ttlr-f ins)
            (ttlr-f out))]
    ;; TODO: how do we know whether τ contains a
    ;; label-reference or not?
    [_ τ]))
