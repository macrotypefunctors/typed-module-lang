#lang racket/base
(require racket/match
         racket/bool
         racket/list
         racket/syntax
         syntax/id-table
         "type.rkt"
         "env/assoc.rkt"
         "util/for-id-table.rkt")
(module+ test
  (require rackunit
           racket/function
           syntax/parse/define
           (for-syntax racket/base
                       racket/syntax)))

;; ---------------------------------------------------------

(provide sig sig? sig-ref
         pi-sig)

;; A Signature is one of:
;;  - Sig
;;  - PiSig

(define sig (procedure-rename hash 'sig))
(define (sig-ref s x) (hash-ref s x #f))
(define (sig? s) (and (hash? s) (immutable? s)))

;; A PiSig is represented with a
;;   (pi-sig Id Signature Signature)

;; The id `x` is a binding position with the scope of `out`
(struct pi-sig [x in out] #:prefab)

;; ---------------------------------------------------------

(provide sig-component sig-component?
         type-opaque-decl type-opaque-decl?
         val-decl val-decl?
         mod-decl mod-decl?)

;; A Sig is represented with a
;;   (Hashof Symbol SigComponent)

;; A SigComponent is a
;;   (sig-component Id SigEntry)
(struct sig-component [id entry] #:prefab)

;; A SigEntry is one of:
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
;;  - (named-reference Id)
;;  - (dot ModPath Symbol)

;; ---------------------------------------------------------

(provide dot dot?
         transform-named-reference
         named-reference-map)

;; A Type is one of:
;;  - BaseType
;;  - (Arrow [Listof Type] Type)
;;  - (named-reference Symbol)
;;  - (dot ModPath Symbol)   <- added by module system

(struct dot [mod type-name] #:prefab)

;; f might take a symbol and turn it into a type,
;; or might take a symbol and turn it into a path?
(define (transform-named-reference τ f)
  (define (tnr-f t)
    (transform-named-reference t f))
  (match τ
    [(dot M x)
     (dot (tnr-f M) x)]
    [(? sig? s)
     (for/hash ([(k v) (in-hash s)])
       (values k
               (match v
                 [(sig-component x entry)
                  ;; TODO: do some capture-avoiding?
                  (sig-component
                   x
                   (match entry
                     [(val-decl τ) (val-decl (tnr-f τ))]
                     [(type-opaque-decl) (type-opaque-decl)]
                     [(type-alias-decl τ) (type-alias-decl (tnr-f τ))]
                     [(mod-decl s) (mod-decl (tnr-f s))]))])))]
    [(pi-sig x A B)
     ;; TODO: scope stuff for x? This function is used for identifier
     ;;       substitution, so it should respect scope somehow. When `x`
     ;;       shadows one of the bindings being substituted, it shouldn't
     ;;       substitute that binding within `B`.
     (pi-sig x (tnr-f A) (tnr-f B))]
    [_
     (type-transform-named-reference/recur τ f transform-named-reference)]))

(define (named-reference-map f τ)
  (transform-named-reference τ (compose named-reference f)))

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
  (match (lookup G x)
    [(mod-binding s) s]
    [_ #f]))

;; Env Id -> Signature or #f
;; return signature defined by given name
(define (env-lookup-signature G x)
  (match (lookup G x)
    [(sig-binding s) s]
    [_ #f]))

;; ---------------------------------------------------------

;; Creating `where` signatures

(provide sig-where)

(define (sig-where base sym type)
  (hash-update base
               sym
    (λ (prev-decl)
      (match prev-decl
        [(sig-component id (type-opaque-decl))
         (sig-component id (type-alias-decl type))]
        [_ (error "can't `where` a non-opaque declaration")]))
    (λ ()
      (error "can't `where` a non-existent declaration"))))

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
  (define env* (extend env (list (list B-x (mod-binding B-in)))))
  (and (signature-matches? env B-in A-in)
       ;; we add B-in to the environment here because it is the most
       ;; specific type that both signatures need to be compatible with
       (signature-matches? env* A-out* B-out)))

;; Sig Id Id -> Sig
;; substitutes module references 'x-from' with 'x-to'
(define (signature-subst-id S x-from x-to)
  (signature-subst S x-from (named-reference x-to)))

;; Sig Id Path -> Sig
;; substites module references 'x-from' with 'path'
(define (signature-subst S x-from path)
  (transform-named-reference
   S
   (λ (x)
     (cond [(and (identifier? x) (free-identifier=? x-from x))
            path]
           [else
            (named-reference x)]))))

;; ---------------------------------------------------------


;; Env Sig Sig -> Bool
(define (sig-matches? env A B)
  ;; A-id->common : [FreeIdTableof CommonId]
  ;; B-id->common : [FreeIdTableof CommonId]
  ;; where CommonId is an identifier to be bound in the extended
  ;; common env
  ;; sym->id : [Hashof Sym CommonId]
  (define sym->id
    (let* ([acc (hash)]
           [acc (for/fold ([acc acc]) ([k (in-hash-keys A)]
                                       #:when (not (hash-has-key? acc k)))
                  (hash-set acc k (generate-temporary k)))]
           [acc (for/fold ([acc acc]) ([k (in-hash-keys B)]
                                       #:when (not (hash-has-key? acc k)))
                  (hash-set acc k (generate-temporary k)))])
      acc))
  (define A-id->common
    (for/free-id-table ([(k v) (in-hash A)])
      (match-define (sig-component id entry) v)
      (values id (hash-ref sym->id k))))
  (define B-id->common
    (for/free-id-table ([(k v) (in-hash B)])
      (match-define (sig-component id entry) v)
      (values id (hash-ref sym->id k))))
  ;; TODO: use this to convert both *defs* and *refs* for
  ;;       types in sigs
  (define (type-map-mod->common m->c t)
    (named-reference-map (λ (x) (free-id-table-ref m->c x x)) t))
  (define (sig-entry-map-mod->common m->c entry)
    (match entry
      [(type-alias-decl t) (type-alias-decl (type-map-mod->common m->c t))]
      [(type-opaque-decl) entry]
      [(val-decl t) (val-decl (type-map-mod->common m->c t))]
      [(mod-decl s) (mod-decl (signature-map-mod->common m->c s))]))

  (define (signature-map-mod->common m->c s)
    (match s
      [(? sig? s)
       (for/hash ([(k v) (in-hash s)])
         (match-define (sig-component x entry) v)
         (values k (sig-component x (sig-entry-map-mod->common m->c entry))))]
      [(pi-sig x A B)
       (pi-sig x
               (signature-map-mod->common m->c A)
               (signature-map-mod->common m->c B))]))

  (define (sig-entry->env-binding m->c entry)
    (match entry
      ;; TODO: submodules
      [(val-decl t) (val-binding (type-map-mod->common m->c t))]
      [(mod-decl s) (mod-binding (signature-map-mod->common m->c s))]
      [comp (type-binding (sig-entry-map-mod->common m->c entry))]))

  ;; extend the env with all the components from A
  ;; REMEMBER: the entries in this env are EnvBindings!
  ;;           refer to the definition of Env
  (define env*
    (extend
     env
     (for/list ([(A-sym A-comp) (in-hash A)])
       (match-define (sig-component _ A-entry) A-comp)
       (list (hash-ref sym->id A-sym)
             (sig-entry->env-binding A-id->common A-entry)))))

  ;; check that all components in B correspond with components in A
  (for/and ([(B-x B-comp) (in-hash B)])
    (define A-comp
      (sig-ref A B-x))
    (and A-comp
         (let ([A-entry (sig-component-entry A-comp)]
               [B-entry (sig-component-entry B-comp)])
           (sig-entry-matches?
            env*
            (sig-entry-map-mod->common A-id->common A-entry)
            (sig-entry-map-mod->common B-id->common B-entry))))))

;; Env SigEntry SigEntry -> Bool
(define (sig-entry-matches? env A B)
  (match* [A B]
    [[(val-decl A) (val-decl B)]
     (type-matches? env A B)]
    [[(type-alias-decl A) (type-alias-decl B)]
     (type-equal? env A B)]
    [[(type-opaque-decl) (type-opaque-decl)]
     #true]
    [[(type-alias-decl _) (type-opaque-decl)]
     #true]
    [[(mod-decl s-A) (mod-decl s-B)]
     (signature-matches? env s-A s-B)]
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
    ;; N are only allowed to be *paths*.

    [[(dot M x) (dot N x)]
     #:when (mod-path-equal? M N)
     #t]
    [[(dot M x) _]
     (=> cont)
     (match (mod-path-lookup env M x)
       [(type-alias-decl A*) (type-matches? env A* B)]
       [_ (cont)])]
    [[_ (dot N y)]
     (=> cont)
     (match (mod-path-lookup env N y)
       [(type-alias-decl B*) (type-matches? env A B*)]
       [_ (cont)])]

    [[_ _]
     ;; TODO: these envs are different. How do we convert between them so
     ;;       that we can call `subtype?` with *it's* notion of environment
     ;;       instead of ours?
     (subtype?/recur env A B type-matches?)]))

;; ModPath ModPath -> Bool
(define (mod-path-equal? M N)
  (define-values [M-base M-syms] (path->base+names M))
  (define-values [N-base N-syms] (path->base+names N))
  (and
   (free-identifier=? M-base N-base)
   (equal? M-syms N-syms)))

;; -----------------------------------------------------

(provide qualify-type
         qualify-sig
         extend-qual-env
         mod-path-lookup)

#|
Interesting Examples:

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
|#

;; Path -> Id [Listof Sym]
(define (path->base+names path)
  (match path
    [(named-reference id)
     (values id '())]
    [(dot path* x)
     (define-values [base xs]
       (path->base+names path*))
     (values base (append xs (list x)))]))


;; a QualEnv is a [FreeIdTableof TypePath]
;; where a TypePath is a (dot ModPath Symbol)

;; QualEnv Sig ModPath -> QualEnv
;; populates the `qenv` with an entry for everything in the
;; `sig`
(define (extend-qual-env qenv sig prefix)
  (for/fold ([qenv qenv])
            ([(sym comp) (in-hash sig)])
    (match-define (sig-component id entry) comp)
    (match entry
      [(or (type-alias-decl _)
           (type-opaque-decl)
           (mod-decl _))
       (free-id-table-set qenv id (dot prefix sym))]
      [_ qenv])))

;; Env ModPath Symbol -> SigEntry or #f
;; returns corresponding sig entry whose types are
;; valid in the scope of 'env'.
(define (mod-path-lookup env path y)
  (define-values [base syms]
    (path->base+names path))

  (define sig
    (env-lookup-module env base))

  (let loop ([sig sig]
             [syms syms]
             ; qenv : QualEnv
             [qenv (make-immutable-free-id-table)]
             ; prefix : ModPath
             [prefix (named-reference base)])
    (and
     (sig? sig)
     (let ([qenv* (extend-qual-env qenv sig prefix)])
       (match syms
         ['()
          (define comp (sig-ref sig y))
          (match comp
            [(sig-component _ entry)
             (qualify-sig-entry qenv* entry)]
            [#f #f])]

         [(cons x xs*)
          (match (sig-ref sig x)
            [(sig-component _ (mod-decl sig*))
             (define prefix* (dot prefix x))
             (loop sig* xs* qenv* prefix*)]
            [_ #f])])))))

;; QualEnv SigEntry -> SigEntry
;; prefix all types & modules in 'entry' with prefixes in 'qenv'
(define (qualify-sig-entry qenv entry)
  (match entry
    [(val-decl ty)        (val-decl (qualify-type qenv ty))]
    [(type-alias-decl ty) (type-alias-decl (qualify-type qenv ty))]
    [(mod-decl sig)       (mod-decl (qualify-sig qenv sig))]
    [(type-opaque-decl)   (type-opaque-decl)]))

;; QualEnv Type -> Type
(define (qualify-type qenv type)
  (transform-named-reference
   type
   (λ (x)
     (match (free-id-table-ref qenv x #f)
       [#f (named-reference x)]
       [path path]))))

(define (qualify-sig qenv sig)
  ;; TODO: avoid captures?
  (for/hash ([(x comp) (in-hash sig)])
    (match-define (sig-component id entry) comp)
    (values x (sig-component id (qualify-sig-entry qenv entry)))))

;; --------------------------------------------------------------

;; Converting internal type environments to "external" signatures

(provide module-bindings->sig)

;; Bindings -> Sig
(define (module-bindings->sig module-envl)
  (for/hash ([p (in-list module-envl)])
    (match-define (list id binding) p)
    (define decl
      (match binding
        [(val-binding τ) (val-decl τ)]
        [(type-binding decl)
         (match decl
           [(type-alias-decl τ) (type-alias-decl τ)]
           [(type-opaque-decl) decl])]

        [(mod-binding sig)
         (mod-decl sig)]))
    ;; convert identifiers into symbols for the outside names
    ;; for the signature
    (values (syntax-e id) (sig-component id decl))))

;; -----------------------------------------------------

(module+ test
  (define-binary-check (check-sig-matches A B)
    (signature-matches? (empty-env) A B))
  (define-binary-check (check-not-sig-matches A B)
    (not (signature-matches? (empty-env) A B)))

  (define-simple-macro (sig [x:id sig-entry:expr] ...)
    #:with [x* ...] (generate-temporaries #'[x ...])
    #:with [[k/v ...] ...] #'[['x (sig-component x sig-entry)] ...]
    (let ([x (quote-syntax x*)] ...)
      (hash k/v ... ...)))
  (define-simple-macro (pi x:id A:expr B:expr)
    #:with x* (generate-temporary #'x)
    (let ([x (quote-syntax x*)]
          [in A])
      (pi-sig x in B)))

  (define empty (hash))
  (define sig-X=int
    (sig
     [X (type-alias-decl (Int))]))
  (define sig-X-opaque
    (sig
     [X (type-opaque-decl)]))

  (check-sig-matches empty empty)
  (check-sig-matches sig-X=int sig-X=int)
  (check-sig-matches sig-X-opaque sig-X-opaque)

  (check-sig-matches sig-X=int sig-X-opaque)
  (check-not-sig-matches sig-X-opaque sig-X=int)


  (define sig-X/Y-x:X
    (sig
     [X (type-opaque-decl)]
     [Y (type-alias-decl (named-reference X))]
     [x (val-decl (named-reference X))]))

  (define sig-X/Y-x:Y
    (sig
     [X (type-opaque-decl)]
     [Y (type-opaque-decl)]
     [x (val-decl (named-reference Y))]))

  (check-sig-matches sig-X/Y-x:X sig-X/Y-x:Y)
  (check-not-sig-matches sig-X/Y-x:Y sig-X/Y-x:X)


  (define sig-X-Y=X
    (sig
     [X (type-opaque-decl)]
     [Y (type-alias-decl (named-reference X))]))

  (define sig-Y-X=Y
    (sig
     [Y (type-opaque-decl)]
     [X (type-alias-decl (named-reference Y))]))

  (check-not-sig-matches sig-X-Y=X sig-Y-X=Y)


  (check-sig-matches
   (sig [v (val-decl (Int))]
        [X (type-alias-decl (Int))]
        [Y (type-alias-decl (Int))])
   (sig [v (val-decl (named-reference X))]
        [X (type-opaque-decl)]
        [Y (type-alias-decl (named-reference X))]))

  (check-sig-matches
   (sig [X (type-opaque-decl)]
        [Y (type-alias-decl (named-reference X))])
   (sig [Y (type-opaque-decl)]))

  ;; -------------------------
  ;; submodules

  (let ([M #'M])
    (define env
      (list
       (list M (mod-binding (sig
                             [Inner
                              (mod-decl (sig [t (type-alias-decl (Int))]))])))))
    (check-true
     (type-matches? env
                    (Int)
                    (dot (dot (named-reference M) 'Inner) 't))))

  ;; -------------------------
  ;; pi sigs

  (let ([I  (sig [t (type-opaque-decl)])]
        [I* (sig [t (type-alias-decl (Int))])]
        [J  (sig [s (type-opaque-decl)] [t (type-opaque-decl)])]
        [J* (sig [s (type-opaque-decl)] [t (type-alias-decl (named-reference s))])])
    (check-sig-matches I* I)
    (check-sig-matches J* J)

    (check-sig-matches
     (pi x I (sig [v (val-decl (dot (named-reference x) 't))]))
     (pi x I* (sig [v (val-decl (dot (named-reference x) 't))])))

    (check-sig-matches
     (pi x I (sig [v (val-decl (dot (named-reference x) 't))]))
     (pi x I* (sig [v (val-decl (Int))])))

    (check-sig-matches
     (pi x J (sig [v (val-decl (dot (named-reference x) 't))]))
     (pi x J* (sig [v (val-decl (dot (named-reference x) 't))])))

    (check-sig-matches
     (pi x J (sig [v (val-decl (dot (named-reference x) 't))]))
     (pi x J* (sig [v (val-decl (dot (named-reference x) 's))])))

    (check-not-sig-matches
     (pi x J (sig [v (val-decl (dot (named-reference x) 't))]))
     (pi x J* (sig [v (val-decl (Int))])))
    )
  )
