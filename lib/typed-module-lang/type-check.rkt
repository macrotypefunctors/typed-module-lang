#lang racket/base

(provide (all-from-out macrotypes-nonstx/type-check)
         sc
         ⊢≫sig⇒
         sig⇒
         cases)

(require macrotypes-nonstx/expand-check-sugar
         macrotypes-nonstx/type-check)

;; TODO: add forms for "typechecking" modules, etc.

;; sc means "sig check"
(define-expand-check-relation sc
  [external-G module-expr -> module-expr- signature-expr]
  [external-G ⊢ module-expr ≫ module-expr- sig⇒ signature-expr]
  [external-G ⊢ module-expr]
  [≫ module-expr- sig⇒ signature-expr]
  #:in-stx module-expr
  #:out-stx module-expr-
  #:stop-ids '()
  #:bad-output
  (raise-syntax-error #f "expected a typed module expression" module-expr))

