#lang racket/base

(provide (all-from-out "core-lang.rkt")
         #%datum
         #%var
         #%dot
         (rename-out [mod-lang-module-begin #%module-begin]
                     [mod-lang-lambda lambda]
                     [mod-lang-lambda λ]
                     [mod-lang-#%app #%app])
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
                    [#%app core-#%app])
         (for-syntax racket/base
                     racket/function
                     racket/hash
                     racket/list
                     racket/match
                     racket/pretty
                     racket/syntax
                     macrotypes-nonstx/type-prop
                     (only-in syntax/parse [attribute @])
                     "type-check.rkt"
                     "sig.rkt"
                     "type.rkt"
                     "util/for-acc.rkt"))

;; --------------------------------------------------------------

;; A whole program for mod-lang follows this rule

(begin-for-syntax
  ;; mod-lang-sc-passes :
  ;; [Listof Stx] -> (values [Listof Stx] Env)
  (define (mod-lang-sc-passes ds)
    (define-values [env ds/1]
      (for/list/acc ([G '()])
                    ([d (in-list ds)])
        (ec G ⊢ d ≫ d- modsigdef⇒ G+)
        (values (append G+ G)
                d-)))
    (values ds/1 env)))

;; The module-begin form.
;; For now, expect a series of define-module forms
;; and print the output environment with the signatures

(define-syntax mod-lang-module-begin
  (syntax-parser
    [(_ d:expr ...)
     (define-values [ds- G]
       (mod-lang-sc-passes (@ d)))
     (pretty-print G)
     #`(#%module-begin #,@ds-)]))

;; --------------------------------------------------------------

;; Converting internal type environments to "external" signatures

(begin-for-syntax
  ;; Env -> Sig
  (define (module-env->sig module-G)
    (define type-ids
      (for/list ([entry (in-list module-G)]
                 #:when (type-binding? (second entry)))
        (first entry)))

    (define type-id-syms
      (map list type-ids (map syntax-e type-ids)))

    (define (resolve-ids τ)
      (type-named-reference-map
       (λ (x)
         (match (assoc x type-id-syms free-identifier=?)
           [#f x]
           [(list _ sym) sym]))
       τ))

    (for/hash ([p (in-list module-G)])
      (match-define (list id binding) p)
      (define decl
        (match binding
          [(val-binding τ) (val-decl (resolve-ids τ))]
          [(type-binding decl)
           (match decl
             [(type-alias-decl τ) (type-alias-decl (resolve-ids τ))]
             [(type-opaque-decl) decl])]))
      ;; convert identifiers into symbols for the signature
      (values (syntax-e id) decl))))

;; --------------------------------------------------------------

(define-typed-syntax #%var
  ;; as a module
  [⊢≫sig⇒
   [G ⊢ #'(_ x:id)]
   (define s
     (or (env-lookup-module G #'x)
         (raise-syntax-error #f "expected a module" #'x)))
   (er ⊢≫sig⇒ ≫ #'x sig⇒ s)]
  ;; as a signature
  [⊢≫signature⇐
   [G ⊢ #'(_ x:id)]
   (define s
     (or (env-lookup-signature G #'x)
         (raise-syntax-error #f "expected a module" #'x)))
   ;; don't return er, return type-stx with a *sig value* instead
   (type-stx s)]
  [else
   #:with (_ . rst) this-syntax
   #'(core-#%var . rst)])

;; --------------------------------------------------------------

(define-typed-syntax #%dot
  ;; as an expression
  [⊢≫⇒
   [G ⊢ #'(_ m:id x:id)]
   (ec G ⊢ #'m ≫ #'m- sig⇒ s)
   (unless (sig? s) (raise-syntax-error #f "expected a mod" #'m))
   (define τ_x
     (match (sig-ref s (syntax-e #'x))
       [(val-decl τ) (qualify-type #'m τ)]
       [_ (raise-syntax-error #f "not a value binding" #'x)]))
   (er ⊢≫⇒ ≫ #'(hash-ref m- 'x) ⇒ τ_x)]

  ;; as a type
  [⊢≫type⇐
   [dke ⊢ #'(_ m:id x:id)]
   (define G (filter (compose mod-binding? second) dke))
   (ec G ⊢ #'m ≫ _ sig⇒ s)
   (unless (sig? s) (raise-syntax-error #f "expected a mod" #'m))
   (define comp (sig-ref s (syntax-e #'x)))
   (unless (or (type-alias-decl? comp) (type-opaque-decl? comp))
     (raise-syntax-error #f "not a type binding" #'x))
   (type-stx (dot (named-reference #'m) (syntax-e #'x)))]
  )

;; --------------------------------------------------------------

(define-typed-syntax define-module
  #:datum-literals [=]
  [⊢≫modsigdef⇒
   [external-G ⊢ #'(_ name:id = m:expr)]
   (ec external-G ⊢ #'m ≫ #'m- sig⇒ s)
   (er ⊢≫modsigdef⇒ ≫ #`(define name m-)
       modsigdef⇒ (list (list #'name (mod-binding s))))])

(define-typed-syntax define-signature
  #:datum-literals [=]
  [⊢≫modsigdef⇒
   [external-G ⊢ #'(_ name:id = s:expr)]
   (define signature (expand-signature external-G #'s))
   (er ⊢≫modsigdef⇒ ≫ #`(define-syntax name #f)
       modsigdef⇒ (list (list #'name (sig-binding signature))))])

;; --------------------------------------------------------------

;; The `mod` form looks sort of like "core-lang.rkt"'s
;; module-begin form, except that it has an output type

(define-typed-syntax mod
  [⊢≫sig⇒
   [external-G ⊢ #'(_ d:expr ...)]
   ;; TODO: how should external-G be handled?
   ;; the module-sig should definitely *not*
   ;; include bindings from the external-G
   #:with name (generate-temporary 'mod)
   #:do [(define-values [ds- module-env]
           (core-lang-tc-passes external-G (@ d)))
         ;; TODO: include the type-env too
         ;; TODO: determine if the above comment is still relevant?
         (define module-sig (module-env->sig module-env))]
   #:with [x ...] (for/list ([entry (in-list module-env)]
                             #:when (val-binding? (second entry)))
                    (first entry))
   #:with [[k/v ...] ...]
   #'[['x x] ...]
   (er ⊢≫sig⇒
       ≫ #`(local [#,@ds-] (hash k/v ... ...))
       sig⇒ module-sig)])

(define-typed-syntax seal
  #:datum-literals [:>]
  [⊢≫sig⇒
   [external-G ⊢ #'(_ m:expr :> s-stx:expr)]
   #:do [(ec external-G ⊢ #'m ≫ #'m- sig⇒ s-actual)
         (define s-expected (expand-signature external-G #'s-stx))]
   #:fail-unless (signature-matches? external-G s-actual s-expected)
   ;; TODO: smaller error messages that say something like
   ;;       "this component is missing" or "this component has the wrong type"
   "signature mismatch"
   (er ⊢≫sig⇒
       ≫ #'m-
       sig⇒ s-expected)])

(define-typed-syntax sig
  #:literals [val type]
  #:datum-literals [: =]
  [⊢≫signature⇐
   [external-G ⊢ #'(_ {~alt (val val-name : val-type)
                            (type alias-name = alias-type)
                            (type opaque-name)}
                      ...)]

   (define dke (map (λ (x) (list x 'type))
                    (append (@ alias-name) (@ opaque-name))))
   (define dke+external
     ;; the things in the dke are "closer"
     (append dke (env->decl-kind-env external-G)))

   (define (expand-type type-stx)
     (expand-type/dke dke+external type-stx))

   (define val-τs (map expand-type (@ val-type)))
   (define alias-τs (map expand-type (@ alias-type)))

   (type-stx
    (module-env->sig
     (append (map list (@ val-name) (map val-binding val-τs))
             (map list (@ alias-name) (map (compose type-binding type-alias-decl) alias-τs))
             (map list (@ opaque-name) (map (const (type-binding (type-opaque-decl))) (@ opaque-name))))))])

;; --------------------------------------------------------------

(define-typed-syntax Π
  #:datum-literals [:]
  [⊢≫signature⇐
   [external-G ⊢ #'(_ ([x:id : A-stx]) B-stx)]
   (define A (expand-signature external-G #'A-stx))
   (define body-G (cons (list #'x (mod-binding A)) external-G))
   (define B (expand-signature body-G #'B-stx))
   (type-stx (pi-sig #'x A B))])

;; --------------------------------------------------------------

(define-typed-syntax mod-lang-lambda
  ;; as a module
  [⊢≫sig⇒
   [G ⊢ #'(_ ([x:id : A-stx]) body-module:expr)]
   (define A (expand-signature G #'A-stx))
   (define body-G (cons (list #'x (mod-binding A)) G))
   (ec body-G ⊢ #'body-module ≫ #'body-module- sig⇒ B)
   (er ⊢≫sig⇒ ≫ #'(λ (x) body-module-) sig⇒ (pi-sig #'x A B))]
  [else
   #:with (_ . rst) this-syntax
   #'(core-lambda . rst)])

;; --------------------------------------------------------------

(define-typed-syntax mod-lang-#%app
  ;; as a module
  [⊢≫sig⇒
     [G ⊢ #'(_ fun ~! arg:id)]
     ;; TODO: allow arg to be arbitrary module expression
     ;;   ... may require figuring out how to solve let vs. submodule ?
     (ec G ⊢ #'fun ≫ #'fun- sig⇒ (pi-sig x A B))
     (ec G ⊢ #'arg ≫ #'arg- sig⇒ A*)
     (unless (signature-matches? G A* A)
       (raise-syntax-error #f "signature mismatch" #'arg))
     (define B* (signature-subst B x #'arg))
     (er ⊢≫sig⇒ ≫ #'(fun- arg-)
         sig⇒ B*)]

  [else
   #:with (_ . rst) this-syntax
   #'(core-#%app . rst)])
