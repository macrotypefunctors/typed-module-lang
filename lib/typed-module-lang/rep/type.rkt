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
;;   - (type-opaque-decl)

(struct type-alias-decl [type] #:prefab)
(struct newtype-decl [id type]
  ; id is the identifier for the constructor
  ; type is the argument to the constructor
  ; NOTE: don't substitute for type during subtype relation
  ;       newtype =/= type alias !
  #:prefab)
(struct type-opaque-decl [] #:prefab)

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
;;   - (Forall [Listof Label] Type)
;;   - (label-reference Label)

(struct Int [] #:prefab)
(struct Bool [] #:prefab)
(struct Arrow [inputs output] #:prefab)
(struct Forall [labels body] #:prefab)
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

    [[(Forall Xs τa-body) (Forall Ys τb-body)]
     (define common-labels
       (map fresh-label Xs))
     (define G+common
       (label-env-extend
        G
        (map (λ (x) (list x (type-binding (type-opaque-decl))))
             common-labels)))
     (and (= (length Xs) (length Ys))
          (let ([τa-body* (type-substitute-label* G Xs common-labels)]
                [τb-body* (type-substitute-label* G Ys common-labels)])
          (recur-subtype? G+common τa-body* τb-body*)))]

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
    [(Forall ls body)
     (Forall ls (ttlr-f body))]
    ;; TODO: how do we know whether τ contains a
    ;; label-reference or not?
    [_ τ]))

;; type-substitute-label* :
;; Type [Listof Label] [Listof Label] -> Type
(define (type-substitute-label* τ Xs-old Xs-new)
  (define mapping
    (make-immutable-hash (map cons Xs-old Xs-new)))
  (type-label-reference-map (λ (X) (hash-ref mapping X X)) τ))

;; type-substitute* :
;; Type [Listof Label] [Listof Type] -> Type
(define (type-substitute* τ Xs-old τs-new)
  (define mapping
    (make-immutable-hash (map cons Xs-old τs-new)))
  (type-transform-label-reference
   τ
   (λ (X) (hash-ref mapping X (label-reference X)))))