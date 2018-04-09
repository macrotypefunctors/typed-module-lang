#lang racket/base

(provide (all-from-out "core-lang.rkt")
         #%datum
         #%var
         (rename-out [mod-lang-module-begin #%module-begin]
                     [mod-lang-lambda lambda]
                     [mod-lang-lambda λ]
                     [core-#%app #%app])
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
                     racket/list
                     racket/match
                     racket/pretty
                     racket/syntax
                     racket/hash
                     macrotypes-nonstx/type-prop
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
       (mod-lang-sc-passes (attribute d)))
     (pretty-print G)
     #`(#%module-begin #,@ds-)]))

;; --------------------------------------------------------------

;; Converting internal type environments to "external" signatures

(begin-for-syntax
  (define (module-env->sig module-G)
    (for/hash ([p (in-list module-G)])
      (match-define (list val-id binding) p)
      (define decl
        (match binding
          [(val-binding type) (val-decl type)]
          [(type-binding type-decl) type-decl]))
      ;; convert identifiers into symbols for the signature
      (values (syntax-e val-id) decl))))

;; --------------------------------------------------------------

(define-typed-syntax #%var
  ;; as a module
  [⊢≫sig⇒
   [G ⊢ #'(_ x:id)]
   (define s
     (match (assoc #'x G free-identifier=?)
       [(list _ (mod-binding s)) s]
       [_ (raise-syntax-error #f "expected a module" #'x)]))
   (er ⊢≫sig⇒ ≫ #'x sig⇒ s)]
  ;; as a signature
  [⊢≫signature⇐
   [G ⊢ #'(_ x:id)]
   ;; don't return er, return type-stx with a *sig value* instead
   (match (assoc #'x G free-identifier=?)
     [(list _ (sig-binding s)) (type-stx s)]
     [_ (raise-syntax-error #f "expected a signature" #'x)])]
  [else
   #:with (_ . rst) this-syntax
   #'(core-#%var . rst)])

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
           (core-lang-tc-passes (attribute d)))
         ;; TODO: include the type-env too
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

   (define dke
     (append (attribute alias-name)
             (attribute opaque-name)))

   ;; [Listof [List Id Symbol]]
   (define type-name->syms
     (for/list ([id (in-list dke)])
       (list id (syntax-e id))))

   (define (resolve-ids τ)
     (type-named-reference-map
      (λ (x)
        (match (assoc x type-name->syms free-identifier=?)
          [#f x]
          [(list _ sym) sym]))
      τ))

   (define val-τs
     (for/list ([type-stx (in-list (attribute val-type))])
       (resolve-ids (expand-type/dke dke type-stx))))

   (define alias-τs
     (for/list ([type-stx (in-list (attribute alias-type))])
       (resolve-ids (expand-type/dke dke type-stx))))

   (type-stx
    (hash-union
     ; values
     (for/hash ([id (in-list (attribute val-name))]
                [τ (in-list val-τs)])
       (values (syntax-e id) (val-decl τ)))
     ; aliases
     (for/hash ([id (in-list (attribute alias-name))]
                [τ (in-list alias-τs)])
       (values (syntax-e id) (type-alias-decl τ)))
     ; opaque types
     (for/hash ([id (in-list (attribute opaque-name))])
       (values (syntax-e id) (type-opaque-decl)))))])


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
