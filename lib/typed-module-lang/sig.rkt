#lang racket/base
(require racket/match
         racket/bool
         "type.rkt")

;; ---------------------------------------------------------

;; A Signature is one of:
;;  - Sig
;;  - PiSig

;; ---------------------------------------------------------

;; A ModExpr is one of:
;;  - Id

;; ---------------------------------------------------------

(provide val-decl)

;; A Sig is represented with a
;;   (Hashof Symbol SigComponent)

;; A SigComponent is one of:
;;  - (type-alias-decl Type)
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

;; A Type is one of:
;;  - BaseType
;;  - (Arrow [Listof Type] Type)
;;  - (named-reference Symbol)
;;  - (dot ModExpr Symbol)
;;  - TODO: ∀

(struct dot [mod type-name] #:prefab)

;; ---------------------------------------------------------

;; An EnvBinding is one of
;;  - SigComponent
;;  - Signature
;; An Env is a [Hash Symbol EnvBinding] representing the types (opaque
;; or alias) and modules (their signatures) in scope.
;; TODO: think about symbols vs. identifiers more!

(define (sig-env->type-env env)
  (for/list ([(x comp) (in-hash env)])
    ('TODO)))


;; TODO: it may be a better idea to use an id-table instead of a hash
;; with symbol keys. need to discuss pros / cons

;; Env Signature Signature -> Bool
(define (signature-matches? env A B)
  (cond
    [(and (hash? A)   (hash? B))   (sig-matches? env A B)]
    [(and (pi-sig? A) (pi-sig? B)) (pi-sig-matches? env A B)]
    [else #f]))

;; Env PiSig PiSig -> Bool
(define (pi-sig-matches? env A B)
  (match-define (pi-sig A-x A-in A-out) A)
  (match-define (pi-sig B-x B-in B-out) B)
  (define A-out* (signature-subst A-out A-x B-x))
  (define env/out (hash-set env (syntax-e B-x) B-in))
  (and (signature-matches? env B-in A-in)
       ;; we add B-in to the environment here because it is the most
       ;; specific type that both signatures need to be compatible with
       (signature-matches? env/out A-out* B-out)))

(define (signature-subst S x-from x-to)
  (unless (free-identifier=? x-from x-to)
    (error "TODO. identifiers not equal"))
  S)

;; ---------------------------------------------------------

;; Env Sig Sig -> Bool
(define (sig-matches? env A B)
  (define env*
    (for/fold ([env* env])
              ([(A-x A-comp) (in-hash A)])
      (hash-set env* A-x A-comp)))

  (for/and ([(B-x B-comp) (in-hash B)])
    (define A-comp
      (hash-ref A B-x #f))
    (and A-comp
         (sig-component-matches? env* A-comp B-comp))))

;; Env SigComp SigComp -> Bool
(define (sig-component-matches? env A B)
  (match* [A B]
    [[(val-decl A) (val-decl B)]
     (type-matches? env A B)]
    [[(type-alias-decl A) (type-alias-decl B)]
     (type-equal? env A B)]
    [[(type-opaque-decl) (type-opaque-decl)]
     #true]
    [[(type-alias-decl _) (type-opaque-decl)]
     #true]
    [[_ _]
     #false]))

;; Env Type Type -> Bool
(define (type-equal? env A B)
  (and (type-matches? env A B)
       (type-matches? env B A)))

;; Env Type Type -> Bool
(define (type-matches? env A B)
  (match* [A B]

    ;; two identical named-reference types are equal; this handles the case of
    ;; two opaque types as well as preemtively matching aliases that
    ;; are obviously the same. if they are not identical then try to
    ;; reduce them by looking up type aliases. if we determine that
    ;; one is an opaque type, then we can fail because the only way
    ;; two opaque types can be the same is if they are referred to by
    ;; the same name. thus they should have been accepted by the
    ;; initial check.

    [[(named-reference x) (named-reference x)] #t]
    [[(named-reference x) _]
     (=> cont)
     (match (lookup env x)
       [(type-alias-decl A*) (type-matches? env A* B)]
       [_ (cont)])]
    [[_ (named-reference y)]
     (=> cont)
     (match (lookup env y)
       [(type-alias-decl B*) (type-matches? env A B*)]
       [_ (cont)])]

    ;; similar for dotted expressions although "M.x <: N.x" requires
    ;; check if "M = N". according to ATAPL this is undecidable in
    ;; general, and there are very confusing circumstances that can
    ;; arise when we try to seal M or N. thus it is easier when M and
    ;; N are only allowed to be identifiers (or paths).

    [[(dot M x) (dot N x)]
     #:when (mod-expr-equal? M N)
     #t]
    [[(dot M x) _]
     (=> cont)
     (match (lookup/mod-expr env M x)
       [(type-alias-decl A*) (type-matches? env A* B)]
       [_ (cont)])]
    [[_ (dot N y)]
     (=> cont)
     (match (lookup/mod-expr env N y)
       [(type-alias-decl B*) (type-matches? env A B*)]
       [_ (cont)])]

    ;; TODO: arrow types

    [[_ _] (equal? A B)]))

;; ModExpr ModExpr -> Bool
(define (mod-expr-equal? M N)
  ;; TODO: handle cases other than ModExpr is an Id
  (free-identifier=? M N))

;; -----------------------------------------------------

;; Env Symbol -> EnvBinding or #f
(define (lookup env x)
  (hash-ref env x #f))

;; Env ModExpr Symbol -> EnvBinding or #f
(define (lookup/mod-expr env M x)
  ;; TODO: handle cases other than ModExpr is an Id
  (match (lookup env (syntax-e M))
    [(? hash? sig)
     (define comp (hash-ref sig x #f))
     (and comp (qualify-component M comp))]
    [_ #f]))

;; ModExpr Component -> Component
;; prefix all named types in the component with module 'M'
(define (qualify-component M comp)
  (match comp
    [(val-decl ty)        (val-decl (qualify-type M ty))]
    [(type-alias-decl ty) (type-alias-decl (qualify-type M ty))]
    [(type-opaque-decl)   (type-opaque-decl)]))

;; ModExpr Type -> Component
(define (qualify-type M type)
  (match type
    [(named-reference x) (dot M x)]
    [(dot M x) (error 'qualify-type "TODO: qualifying a dot type?")]
    [_ type]))

;; -----------------------------------------------------

(module+ test
  (require rackunit racket/function)
  (define-binary-check (check-sig-matches A B)
    (signature-matches? (hash) A B))
  (define-binary-check (check-not-sig-matches A B)
    (not (signature-matches? (hash) A B)))

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
     'Y (type-alias-decl (named-reference 'X))
     'x (val-decl (named-reference 'X))))

  (define sig-X/Y-x:Y
    (sig
     'X (type-opaque-decl)
     'Y (type-opaque-decl)
     'x (val-decl (named-reference 'Y))))

  (check-sig-matches sig-X/Y-x:X sig-X/Y-x:Y)
  (check-not-sig-matches sig-X/Y-x:Y sig-X/Y-x:X)


  (define sig-X-Y=X
    (sig
     'X (type-opaque-decl)
     'Y (type-alias-decl (named-reference 'X))))

  (define sig-Y-X=Y
    (sig
     'Y (type-opaque-decl)
     'X (type-alias-decl (named-reference 'Y))))

  (check-not-sig-matches sig-X-Y=X sig-Y-X=Y)


  (check-sig-matches
   (sig 'v (val-decl (Int))
        'X (type-alias-decl (Int))
        'Y (type-alias-decl (Int)))
   (sig 'v (val-decl (named-reference 'X))
        'X (type-opaque-decl)
        'Y (type-alias-decl (named-reference 'X))))

  (check-sig-matches
   (sig 'X (type-opaque-decl)
        'Y (type-alias-decl (named-reference 'X)))
   (sig 'Y (type-opaque-decl)))

  (let ([x #'x]
        [I  (sig 't (type-opaque-decl))]
        [I* (sig 't (type-alias-decl (Int)))]
        [J  (sig 's (type-opaque-decl) 't (type-opaque-decl))]
        [J* (sig 's (type-opaque-decl) 't (type-alias-decl (named-reference 's)))])
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
