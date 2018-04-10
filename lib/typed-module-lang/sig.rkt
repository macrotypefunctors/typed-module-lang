#lang racket/base
(require racket/match
         racket/bool
         "type.rkt")

;; ---------------------------------------------------------

(provide sig sig? sig-ref
         pi-sig)

;; A Signature is one of:
;;  - Sig
;;  - PiSig

(define sig (procedure-rename hash 'sig))
(define sig-ref (procedure-rename hash-ref 'sig-ref))
(define (sig? s) (and (hash? s) (immutable? s)))

;; A PiSig is represented with a
;;   (pi-sig Id Signature Signature)

;; The id `x` is a binding position with the scope of `out`
(struct pi-sig [x in out] #:prefab)

;; ---------------------------------------------------------

(provide type-opaque-decl type-opaque-decl?
         val-decl val-decl?)

;; A Sig is represented with a
;;   (Hashof Symbol SigComponent)

;; A SigComponent is one of:
;;  - (type-alias-decl Type)
;;  - (type-opaque-decl)
;;  - (val-decl Type)
;; TODO: newtype-decl
;;  - (mod-decl Signature)

; type-alias-decl from "type.rkt"
(struct type-opaque-decl [] #:prefab)
(struct val-decl [type] #:prefab)
(struct mod-decl [type] #:prefab)

;; ---------------------------------------------------------

;; A ModExpr is one of:
;;  - ModPath
;;  - (mod ...)
;;  ... TODO: other things

;; A ModPath is one of:
;;  - Id
;;  - (dot ModPath Symbol)

;; ---------------------------------------------------------

(provide dot dot?)

;; A Type is one of:
;;  - BaseType
;;  - (Arrow [Listof Type] Type)
;;  - (named-reference Symbol)
;;  - (dot ModPath Symbol)   <- added by module system

(struct dot [mod type-name] #:prefab)

;; ---------------------------------------------------------

(provide mod-binding mod-binding?
         sig-binding sig-binding?
         env-lookup-module
         env-lookup-signature)

;; a DeclKindEnv is a [Listof [List Id DeclKind]]
;;   - 'type
;;   - 'val
;;   - (mod-binding Signature)  <- added by module system

;; an Env is a [Listof [List Id EnvBinding]], just as in "type.rkt"
;; an EnvBinding is one of
;;   - (val-binding Type)
;;   - (type-binding TypeDecl)
;;   - (mod-binding Signature)    <- added by module system
;;   - (sig-binding Signature)    <- added by module system
;; a TypeDecl is one of
;;   - (type-alias-decl Type)
;;   - (newtype-decl Id Type)
;;   - (type-opaque-decl)   <- added by module system

(struct mod-binding [sig] #:prefab)
(struct sig-binding [sig] #:prefab)

;; TODO: it may be a better idea to use an id-table instead of a hash
;; with symbol keys. need to discuss pros / cons

;; Env Id -> Signature or #f
;; return signature of module with given name
(define (env-lookup-module G x)
  (match (assoc x G free-identifier=?)
    [(list _ (mod-binding s)) s]
    [_ #f]))

;; Env Id -> Signature or #f
;; return signature defined by given name
(define (env-lookup-signature G x)
  (match (assoc x G free-identifier=?)
    [(list _ (sig-binding s)) s]
    [_ #f]))

;; ---------------------------------------------------------

(provide signature-matches?
         type-matches?
         signature-subst)

;; Env Signature Signature -> Bool
(define (signature-matches? env A B)
  (cond
    [(and (hash? A)   (hash? B))   (sig-matches? env A B)]
    [(and (pi-sig? A) (pi-sig? B)) (pi-sig-matches? env A B)]
    [else #f]))

;; Env PiSig PiSig -> Bool
(define (pi-sig-matches? env A B)
  ;; A-x and B-x are already Id! no need to promote symbols to ids
  ;; like what had to be done for sig matching.
  ;; still, we have to substitue the argument names. it is arbitrary
  ;; which one we substitue as long as they are equal when matching
  ;; the range signatures.
  (match-define (pi-sig A-x A-in A-out) A)
  (match-define (pi-sig B-x B-in B-out) B)
  (define A-out* (signature-subst-id A-out A-x B-x))
  (define env* (cons (list B-x (mod-binding B-in)) env))
  (and (signature-matches? env B-in A-in)
       ;; we add B-in to the environment here because it is the most
       ;; specific type that both signatures need to be compatible with
       (signature-matches? env* A-out* B-out)))

;; Sig Id Id -> Sig
;; substitutes module references 'x-from' with 'x-to'
(define (signature-subst-id S x-from x-to)
  (unless (free-identifier=? x-from x-to)
    (error 'signature-subst-id "TODO. identifiers not equal"))
  S)

;; Sig Id Path -> Sig
;; substites module references 'x-from' with 'path'
;; TODO: ????????????????????
(define (signature-subst S x-from path)
  (unless (identifier? path)
    (error 'signature-subst "TODO: paths?"))
  (signature-subst-id S x-from path))

;; ---------------------------------------------------------


;; Env Sig Sig -> Bool
(define (sig-matches? env A B)
  ;; TODO: use this to convert both *defs* and *refs* for
  ;;       types in sigs
  (define (sig-sym->id sym)
    (datum->syntax #f sym))
  (define (type-map-sym->id t)
    (type-named-reference-map sig-sym->id t))
  (define (sig-component-map-sym->id comp)
    (match comp
      [(type-alias-decl t) (type-alias-decl (type-map-sym->id t))]
      [(type-opaque-decl) comp]
      [(val-decl t) (val-decl (type-map-sym->id t))]))

  (define (sig-component->env-binding comp)
    (match comp
      [(val-decl t) (val-binding (type-map-sym->id t))]
      [comp (type-binding (sig-component-map-sym->id comp))]))

  ;; extend the env with all the components from B
  ;; REMEMBER: the entries in this env are EnvBindings!
  ;;           refer to the definition of Env
  (define env*
    (for/fold ([env* env])
              ([(A-x A-comp) (in-hash A)])
      (cons (list (sig-sym->id A-x)
                  (sig-component->env-binding A-comp))
            env*)))

  ;; check that all components in B correspond with components in A
  (for/and ([(B-x B-comp) (in-hash B)])
    (define A-comp
      (hash-ref A B-x #f))
    (and A-comp
         (sig-component-matches? env*
                                 (sig-component-map-sym->id A-comp)
                                 (sig-component-map-sym->id B-comp)))))

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

    ;; type matching for dotted expressions "M.x <: N.x" requires a
    ;; check if "M = N". according to ATAPL this is undecidable in
    ;; general, and there are very confusing circumstances that can
    ;; arise when we try to seal M or N. thus it is easier when M and
    ;; N are only allowed to be identifiers (or paths).

    [[(dot M x) (dot N x)]
     #:when (mod-expr-equal? M N)
     #t]
    [[(dot M x) _]
     (=> cont)
     (match (mod-expr-lookup env M x)
       [(type-alias-decl A*) (type-matches? env A* B)]
       [_ (cont)])]
    [[_ (dot N y)]
     (=> cont)
     (match (mod-expr-lookup env N y)
       [(type-alias-decl B*) (type-matches? env A B*)]
       [_ (cont)])]

    [[_ _]
     ;; TODO: these envs are different. How do we convert between them so
     ;;       that we can call `subtype?` with *it's* notion of environment
     ;;       instead of ours?
     (subtype?/recur env A B type-matches?)]))

;; ModExpr ModExpr -> Bool
(define (mod-expr-equal? M N)
  ;; TODO: handle cases other than ModExpr is an Id
  (free-identifier=? M N))

;; -----------------------------------------------------

(provide qualify-type)

N : (sig (type C))

M = (mod
     (type A)
     (define-module J : (sig (type D)))
     (define-module L :
       (sig
        (type B)
        (type T1 = A)
        (type T2 = B)
        (type T3 = N.C)
        (type T4 = J.D))))

A must have M.
J must have M.
B must have M.L.

M.L : (sig (type B)
           (type T1 = M.A)
           (type T2 = B))

M.L.T1 = (alias M.A)
M.L.T2 = (alias M.L.B)
M.L.T3 = (alias N.C)
M.L.T4 = (alias M.J.D)

;; Path -> Id [Listof Sym]
(define (path->base+names path)
  (match path
    [(? identifier? id)
     (values id '())]
    [(dot path* x)
     (define-values [base xs]
       (path->base+names path*))
     (values base (append xs (list x)))]))


;; a QualEnv is a [Hashof Symbol ModPath]

;; Env ModPath Symbol -> SigComp or #f
;; returns corresponding component whose types are
;; valid in the scope of 'env'.
(define (mod-path-lookup env path y)
  (define-values [base xs]
    (path->base+names path))

  ;; QualEnv Sig ModPath -> QualEnv
  (define (extend-qual-env qenv sig prefix)
    (for/fold ([qenv qenv])
              ([(x comp) (in-hash sig)])
      (match comp
        [(or (type-alias-decl _)
             (type-opaque-decl)
             (mod-decl _))
         (hash-set qenv x prefix)]
        [_ qenv])))

  (define sig
    (env-lookup-module env base))

  (let loop ([sig sig]
             [xs xs]
             [qenv '()]
             [prefix base])
    (and
     (sig? sig)
     (let ([qenv* (extend-qual-env qenv sig prefix)])
       (match xs
         ['()
          (define comp (sig-ref sig y #f))
          (and comp (qualify-component qenv comp))]

         [(cons x xs*)
          (match (sig-ref sig x #f)
            [(mod-decl sig*)
             (define path* (dot path x))
             (loop sig* xs* qenv* path*)]
            [_ #f])])))))

;; QualEnv SigComp -> SigComp
;; prefix all types & modules in 'comp' with prefixes in 'qenv'
(define (qualify-component qenv comp)
  (match comp
    [(val-decl ty)        (val-decl (qualify-type qenv ty))]
    [(type-alias-decl ty) (type-alias-decl (qualify-type qenv ty))]
    [(mod-decl sig)       (mod-decl (qualify-sig qenv sig))]
    [(type-opaque-decl)   (type-opaque-decl)]))

;; QualEnv Type -> Type
(define (qualify-type qenv type)
  (define (qual τ) (qualify-type qenv τ))
  (match type
    [(named-reference x)
     (match (hash-ref qenv x #f)
       [#f type]
       [prefix (dot prefix x)])]
    [(dot path x)
     ;; TODO: how to qualify module paths?
     ;;  probably should use path->base+names to split
     ;;  path and qualify the base part
     (error 'qualify-type "TODO: qualifying a dot type?")]
    [(Arrow ins out) (Arrow (map qual ins) (qual out))]
    [_
     ;; TODO: how do we know if the type contains more
     ;;  references?
     type]))

;; -----------------------------------------------------

(module+ test
  (require rackunit racket/function)
  (define-binary-check (check-sig-matches A B)
    (signature-matches? '() A B))
  (define-binary-check (check-not-sig-matches A B)
    (not (signature-matches? '() A B)))

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
