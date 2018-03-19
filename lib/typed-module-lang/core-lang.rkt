#lang racket/base

(provide Int
         ->
         val
         (rename-out [core-lang-module-begin #%module-begin])
         #%datum
         #%var
         )

(require syntax/parse/define
         macrotypes-nonstx/type-macros
         (for-syntax racket/base
                     racket/match
                     racket/syntax
                     macrotypes-nonstx/type-prop
                     "type-check.rkt"))

;; ----------------------------------------------------

(define-base-type Int)
(define-type-constructor Arrow [inputs output])

(define-syntax-parser ->
  [(-> in* ... out*)
   (define ins (map expand-type (attribute in*)))
   (define out (expand-type #'out*))
   (type-stx (Arrow ins out))])

;; ----------------------------------------------------

;; A "whole program" for core-lang follows this rule

(define-syntax core-lang-module-begin
  (syntax-parser
    [(_ d:expr ...)
     (define-values [module-G revds]
       (for/fold ([G '()]
                  [revds '()])
                 ([d (in-list (attribute d))])
         (ec G ⊢ d ≫ d- def⇒ G*)
         (values G* (cons d- revds))))
     #`(#%module-begin
        #,@(for/list ([d (in-list (reverse revds))])
             (tc-in module-G d)))]))

;; ----------------------------------------------------

;; core-def forms:
;;  - val
;;  - type
;;  - newtype

(define-typed-syntax val
  #:datum-literals [: =]
  [⊢≫def⇒
   ; this G will include *only* previous definitions
   ; DO NOT typecheck e in this context
   [G ⊢ #'(_ x:id : τ-stx:expr = e:expr)]
   (define τ (expand-type #'τ-stx))
   (er ⊢≫def⇒ ≫ #`(val/pass-2 x : #,(type-stx τ) e)
       def⇒ (cons (list #'x τ) G))])

(define-syntax-parser val/pass-2
  #:datum-literals [:]
  [(_ x : τ-stx e)
   (match this-syntax
     [(tc-in G _)
      ; this G will include all top-level definitions in the program
      ; e can only be typechecked in *this* G
      (define τ (expand-type #'τ-stx))
      (ec G ⊢ #'e ≫ #'e- ⇐ τ)
      #`(define x e-)])])

;; ----------------------------------------------------

;; core-expr forms:
;;  - #%datum
;;  - #%app
;;  - λ
;;  - #%var
;;  - Λ
;;  - inst

;; for now, no `inst` type inference

(define-typed-syntax #%datum
  [⊢≫⇒
   [G ⊢ #'(_ . i:exact-integer)]
   (er ⊢≫⇒ ≫ #''i ⇒ (Int))])

(define-typed-syntax #%var
  [⊢≫⇒
   [G ⊢ #'(_ x:id)]
   (match-define (list _ τ) (assoc #'x G free-identifier=?))
   (er ⊢≫⇒ ≫ #'x ⇒ τ)])

;; ----------------------------------------------------

