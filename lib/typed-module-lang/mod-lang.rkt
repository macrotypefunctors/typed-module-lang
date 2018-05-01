#lang racket/base

(provide (all-from-out "core-lang.rkt")
         #%datum
         #%var
         #%dot
         (rename-out [mod-lang-module-begin #%module-begin]
                     [mod-lang-lambda lambda]
                     [mod-lang-lambda λ]
                     [mod-lang-#%app #%app]
                     [mod-lang-where where]
                     [core-let let])
         module
         define-module
         mod
         seal
         define-signature
         sig
         Π)

(require syntax/parse/define
         racket/local
         macrotypes-nonstx/type-macros
         (rename-in (except-in "core-lang.rkt" #%module-begin λ)
                    [#%var core-#%var]
                    [lambda core-lambda]
                    [let core-let]
                    [#%app core-#%app])
         (for-syntax racket/base
                     racket/function
                     racket/hash
                     racket/list
                     racket/match
                     racket/pretty
                     racket/syntax
                     unstable/match
                     macrotypes-nonstx/type-prop
                     (only-in syntax/parse [attribute @])
                     "type-check.rkt"
                     "sig.rkt"
                     "type.rkt"
                     "env/assoc.rkt"
                     "print/print-type.rkt"
                     "print/print-env.rkt"
                     "util/for-acc.rkt"))

;; --------------------------------------------------------------

;; A whole program for mod-lang follows this rule

(begin-for-syntax
  ;; mod-body-tc-passes :
  ;; Env [Listof Stx] -> (values [Listof Stx] Bindings)
  (define (mod-body-tc-passes external-G ds)
    (define-values [module-bindings ds/0]
      (for/list/acc ([Gl '()])
                    ([d (in-list ds)])
        (define G+external (extend external-G Gl))
        (ec G+external ⊢md d ≫ d- submoddef⇒ Gl+)
        (values (append Gl+ Gl)
                d-)))
    (define G+modules (extend external-G module-bindings))
    (define-values [ds/1234 module-envl]
      (core-lang-tc-passes G+modules ds/0))
    (values ds/1234 (append module-envl module-bindings)))

  ;; mod-lang-sc-passes :
  ;; [Listof Stx] -> (values [Listof Stx] Bindings)
  (define (mod-lang-sc-passes ds)
    (define external (empty-env))
    (define-values [envl ds/1]
      (for/list/acc ([Gl '()])
                    ([d (in-list ds)])
        (define G+external (extend external Gl))
        (ec G+external ⊢md d ≫ d- modsigdef⇒ Gl+)
        (values (append Gl+ Gl)
                d-)))
    (values ds/1 envl)))

;; The module-begin form.
;; For now, expect a series of define-module forms
;; and print the output environment with the signatures

(define-syntax mod-lang-module-begin
  (syntax-parser
    [(_ d:expr ...)
     (define-values [ds- bindings]
       (mod-lang-sc-passes (@ d)))
     (print-env bindings)
     #`(#%module-begin #,@ds-)]))

;; --------------------------------------------------------------

(define-typed-syntax #%var
  ;; as a module
  [⊢m≫sig⇒
   [G ⊢m #'(_ x:id)]
   (define s
     (or (env-lookup-module G #'x)
         (raise-syntax-error #f "expected a module" #'x)))
   (er ⊢m≫sig⇒ ≫ #'x sig⇒ s)]
  ;; as a signature
  [⊢s≫signature⇐
   [G ⊢s #'(_ x:id)]
   (define s
     (or (env-lookup-signature G #'x)
         (raise-syntax-error #f "expected a module" #'x)))
   ;; don't return er, return type-stx with a *sig value* instead
   (type-stx s)]
  [else
   #:with (_ . rst) this-syntax
   (syntax/loc this-syntax (core-#%var . rst))])

;; --------------------------------------------------------------

(begin-for-syntax
  (define-syntax-class module-path
    #:attributes (path)
    (pattern ((~literal #%dot) M:module-path x:id)
             #:attr path (dot (attribute M.path) (syntax-e #'x)))
    (pattern x:id
             #:attr path (named-reference #'x))))

(define-typed-syntax #%dot
  ;; as an expression
  [⊢e≫⇒
   [G ⊢e #'(_ m:module-path x:id)]
   (ec G ⊢m #'m ≫ #'m- sig⇒ s)
   (unless (sig? s) (raise-syntax-error #f "expected a mod" #'m))
   (define τ_x
     (match (mod-path-lookup G (attribute m.path) (syntax-e #'x))
       [(val-decl τ) τ]
       [_ (raise-syntax-error #f "not a value binding" #'x)]))
   (er ⊢e≫⇒ ≫ #'(hash-ref m- 'x) ⇒ τ_x)]

  ;; as a type
  [⊢τ≫type⇐
   [dke ⊢τ #'(_ m:module-path x:id)]
   (define G (filter (compose mod-binding? second) dke))
   (ec G ⊢m #'m ≫ _ sig⇒ s)
   (unless (sig? s) (raise-syntax-error #f "expected a mod" #'m))
   (define comp (sig-ref s (syntax-e #'x)))
   (unless (match? comp (sig-component _ (or (type-alias-decl _) (type-opaque-decl))))
     (raise-syntax-error #f "not a type binding" #'x))
   (type-stx (dot (attribute m.path) (syntax-e #'x)))]

  ;; as a module expression
  [⊢m≫sig⇒
   [G ⊢m #'(_ m:module-path x:id)]
   (ec G ⊢m #'m ≫ #'m- sig⇒ s)
   (unless (sig? s) (raise-syntax-error #f "expected a mod" #'m))
   (define s_x
     (match (mod-path-lookup G (attribute m.path) (syntax-e #'x))
       [(mod-decl m-sig) m-sig]
       [_ (raise-syntax-error #f "not a submodule" #'x)]))

   (er ⊢m≫sig⇒ ≫ #'(hash-ref m- 'x)
       sig⇒ s_x)])


;; --------------------------------------------------------------

(define-typed-syntax define-module
  #:datum-literals [=]
  ;; used in toplevel
  [⊢md≫moddef⇒
   [external-G ⊢md #'(_ name:id = m:expr)]
   (ec external-G ⊢m #'m ≫ #'m- sig⇒ s)
   (er ⊢md≫moddef⇒ ≫ #`(define-module/pass-1234 name m-)
       moddef⇒ (list (list #'name (mod-binding s))))])

(define-typed-syntax define-module/pass-1234
  ;; pass 1 of core-lang-tc-passes
  [⊢≫decl-kinds⇒ [⊢ stx] (er ⊢≫decl-kinds⇒ ≫ stx decl-kinds⇒ '())]
  ;; pass 2 of core-lang-tc-passes
  [⊢≫decl⇒ [_ ⊢ stx] (er ⊢≫decl⇒ ≫ stx decl⇒ '())]
  ;; pass 3 of cole-rang-tc-passes
  [⊢≫val-def⇐ [_ ⊢ stx] (er ⊢≫val-def⇐ ≫ stx)]
  ;; else
  [else
   #:with (_ name m-) this-syntax
   #'(define name m-)])

(define-typed-syntax define-signature
  #:datum-literals [=]
  [⊢md≫modsigdef⇒
   [external-G ⊢md #'(_ name:id = s:expr)]
   (define signature (expand-signature external-G #'s))
   (er ⊢md≫modsigdef⇒ ≫ #`(define-syntax name #f)
       modsigdef⇒ (list (list #'name (sig-binding signature))))])

;; --------------------------------------------------------------

;; The `mod` form looks sort of like "core-lang.rkt"'s
;; module-begin form, except that it has an output type

(define-typed-syntax mod
  [⊢m≫sig⇒
   [external-G ⊢m #'(_ d:expr ...)]
   ;; TODO: how should external-G be handled?
   ;; the module-sig should definitely *not*
   ;; include bindings from the external-G
   #:with name (generate-temporary 'mod)
   #:do [(define-values [ds- module-bindings]
           (mod-body-tc-passes external-G (@ d)))
         ;; TODO: include the type-env too
         ;; TODO: determine if the above comment is still relevant?
         (define module-sig (module-bindings->sig module-bindings))]
   #:with [x ...] (for/list ([entry (in-list module-bindings)]
                             #:when (or (val-binding? (second entry))
                                        (mod-binding? (second entry))))
                    (first entry))
   #:with [[k/v ...] ...]
   #'[['x x] ...]
   (er ⊢m≫sig⇒
       ≫ #`(let () #,@ds- (hash k/v ... ...))
       sig⇒ module-sig)])

(define-typed-syntax seal
  #:datum-literals [:>]
  [⊢m≫sig⇒
   [external-G ⊢m #'(_ m:expr :> s-stx:expr)]
   #:do [(ec external-G ⊢m #'m ≫ #'m- sig⇒ s-actual)
         (define s-expected (expand-signature external-G #'s-stx))]
   #:fail-unless (signature-matches? external-G s-actual s-expected)
   ;; TODO: smaller error messages that say something like
   ;;       "this component is missing" or "this component has the wrong type"
   (format "signature mismatch:\n  expected: ~a\n  given:    ~a\n"
           (sig->string s-expected)
           (sig->string s-actual))
   (er ⊢m≫sig⇒
       ≫ #'m-
       sig⇒ s-expected)])

(define-syntax module
  (λ (stx)
    (raise-syntax-error #f "`module` only valid in sig syntax" stx)))

(define-typed-syntax sig
  #:literals [val type module]
  #:datum-literals [: =]
  [⊢s≫signature⇐
   [external-G ⊢s #'(_ {~alt (module mod-name : mod-sig)
                             (val val-name : val-type)
                             (type alias-name = alias-type)
                             (type opaque-name)
                             }
                       ...)]

   (define-values [G+modules sigs]
     (for/list/acc ([G external-G])
                   ([x (in-list (@ mod-name))]
                    [sig-stx (in-list (@ mod-sig))])
       (define sig (expand-signature G sig-stx))
       (values (extend G (list (list x (mod-binding sig))))
               sig)))

   (define dke
     ;; TODO: check for duplicate identifiers
     (append (map (λ (x s) (list x (mod-binding s))) (@ mod-name) sigs)
             (map (λ (x) (list x 'type)) (@ alias-name))
             (map (λ (x) (list x 'type)) (@ opaque-name))))

   (define dke+external-G
     ;; the things in the dke are "closer"
     (extend (env->decl-kind-env external-G) dke))

   (define (expand-type type-stx)
     (expand-type/dke dke+external-G type-stx))

   (define val-τs   (map expand-type (@ val-type)))
   (define alias-τs (map expand-type (@ alias-type)))

   (type-stx
    (module-bindings->sig
     (append (map list (@ mod-name) (map mod-binding sigs))
             (map list (@ val-name) (map val-binding val-τs))
             (map list (@ alias-name) (map (compose type-binding type-alias-decl) alias-τs))
             (map list (@ opaque-name) (map (const (type-binding (type-opaque-decl))) (@ opaque-name))))))])

;; --------------------------------------------------------------

(define-typed-syntax Π
  #:datum-literals [:]
  [⊢s≫signature⇐
   [external-G ⊢s #'(_ ([x:id : A-stx]) B-stx)]
   (define A (expand-signature external-G #'A-stx))
   (define body-G (extend external-G (list (list #'x (mod-binding A)))))
   (define B (expand-signature body-G #'B-stx))
   (type-stx (pi-sig #'x A B))])

;; --------------------------------------------------------------

(define-typed-syntax mod-lang-lambda
  ;; as a module
  [⊢m≫sig⇒
   [G ⊢m #'(_ ([x:id : A-stx]) body-module:expr)]
   (define A (expand-signature G #'A-stx))
   (define body-G (extend (list (list #'x (mod-binding A)))))
   (ec body-G ⊢m #'body-module ≫ #'body-module- sig⇒ B)
   (er ⊢m≫sig⇒ ≫ #'(λ (x) body-module-) sig⇒ (pi-sig #'x A B))]
  [else
   #:with (_ . rst) this-syntax
   #'(core-lambda . rst)])

;; --------------------------------------------------------------

(define-typed-syntax mod-lang-#%app
  ;; as a module
  [⊢m≫sig⇒
     [G ⊢m #'(_ fun ~! arg:module-path)]
     ;; TODO: allow arg to be arbitrary module expression
     ;;   ... may require figuring out how to solve let vs. submodule ?
     (ec G ⊢m #'fun ≫ #'fun- sig⇒ (pi-sig x A B))
     (ec G ⊢m #'arg ≫ #'arg- sig⇒ A*)
     (unless (signature-matches? G A* A)
       (raise-syntax-error #f
         (format "signature mismatch\n  expected: ~a\n  given:    ~a"
                 (sig->string A) (sig->string A*))
         #'arg))
     (define B* (signature-subst B x (attribute arg.path)))
     (er ⊢m≫sig⇒ ≫ #'(fun- arg-)
         sig⇒ B*)]

  [else
   #:with (_ . rst) this-syntax
   (syntax/loc this-syntax (core-#%app . rst))])

;; --------------------------------------------------------------

(define-typed-syntax mod-lang-where
  #:datum-literals [=]
  ;; as a signature (only use)
  [⊢s≫signature⇐
   [G ⊢s #'(_ base-sig:id type-id:id = τ-stx:expr)]
   (define base (expand-signature G #'base-sig))
   (define sym (syntax-e #'type-id))
   (define τ (expand-type/dke (env->decl-kind-env G) #'τ-stx))
   ;; TODO: how to preserve the scope that the `τ` should be in?
   ;;       (avoid capturing definitions from the base sig)
   (type-stx
    (sig-where base sym τ))])

;; --------------------------------------------------------------
