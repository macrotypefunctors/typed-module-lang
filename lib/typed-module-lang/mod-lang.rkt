#lang racket/base

(provide (all-from-out "core-lang.rkt")
         (rename-out [temporary-module-begin #%module-begin])
         mod)

(require syntax/parse/define
         macrotypes-nonstx/type-macros
         (except-in "core-lang.rkt" #%module-begin)
         (for-syntax racket/base
                     racket/match
                     racket/syntax
                     macrotypes-nonstx/type-prop
                     "type-check.rkt"
                     "sig.rkt"))

;; *Temporary* module-begin form.
;; For now, expect a single module-expr
;; and print its signature

(define-syntax temporary-module-begin
  (syntax-parser
    [(_ m:expr)
     (ec '() ⊢ #'m ≫ #'m- sig⇒ sig)
     (println sig)
     #'(#%module-begin
        m-)]))

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

;; The `mod` form looks sort of like "core-lang.rkt"'s
;; module-begin form, except that it has an output type

(define-typed-syntax mod
  [⊢≫sig⇒
   [external-G ⊢ #'(_ d:expr ...)]
   ;; TODO: how should external-G be handled?
   ;; the module-sig should definitely *not*
   ;; include bindings from the external-G
   #:with name (generate-temporary 'mod)
   (define-values [ds- type-env val-env]
     (core-lang-tc-passes (attribute d)))
   ;; TODO: include the type-env too
   (define module-sig (module-env->sig val-env))
   (er ⊢≫sig⇒
       ≫ #`(begin #,@ds-)
       sig⇒ module-sig)])

;; --------------------------------------------------------------