#lang racket/base

(provide (all-from-out "core-lang.rkt")
         (rename-out [mod-lang-module-begin #%module-begin])
         define-module
         mod)

(require syntax/parse/define
         macrotypes-nonstx/type-macros
         (except-in "core-lang.rkt" #%module-begin)
         (for-syntax racket/base
                     racket/match
                     racket/pretty
                     racket/syntax
                     macrotypes-nonstx/type-prop
                     "type-check.rkt"
                     "sig.rkt"
                     "util/for-acc.rkt"))

;; --------------------------------------------------------------

;; A whole program for mod-lang follows this rule

(begin-for-syntax
  ;; mod-lang-sc-passes :
  ;; [Listof Stx] -> (values [Listof Stx] ???Env)
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
      (match-define (list val-id val-type) p)
      ;; convert identifiers into symbols for the signature
      (values (syntax-e val-id)
              (val-decl val-type)))))

;; --------------------------------------------------------------

(define-typed-syntax define-module
  #:datum-literals [=]
  [⊢≫modsigdef⇒
   [external-G ⊢ #'(_ name:id = m:expr)]
   (ec external-G ⊢ #'m ≫ #'m- sig⇒ s)
   (er ⊢≫modsigdef⇒ ≫ #`(begin (define-syntax name #f) m-)
       modsigdef⇒ (list (list #'name s)))])

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
   (define-values [ds- module-env]
     (core-lang-tc-passes (attribute d)))
   ;; TODO: include the type-env too
   (define module-sig (module-env->sig module-env))
   (er ⊢≫sig⇒
       ≫ #`(begin #,@ds-)
       sig⇒ module-sig)])

;; --------------------------------------------------------------