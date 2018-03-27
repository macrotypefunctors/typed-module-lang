#lang racket/base

(provide (all-from-out macrotypes-nonstx/type-check)
         (all-defined-out)
         cases)

(require racket/list
         racket/match
         macrotypes-nonstx/expand-check-sugar
         macrotypes-nonstx/type-prop
         macrotypes-nonstx/type-check)

;; -------------------------------------------------------------------
;; type checking within a mod

;; which declarations exist? what kind of declarations are they?
(define-expand-check-relation tc/decl-kinds
  ;; intro-kinds : DeclKindEnv
  [decl -> decl- intro-kinds]
  [⊢ decl ≫ decl- decl-kinds⇒ intro-kinds]
  [⊢ decl]
  [≫ decl- decl-kinds⇒ intro-kinds]
  #:in-stx decl
  #:out-stx decl-
  #:stop-ids '()
  #:bad-output (raise-syntax-error #f "expected a type or val declaration" decl))

;; expand types within declarations to build the module's environment
;; TODO: when do we check for recursion in type aliases? what information do we need?
(define-expand-check-relation tc/decl
  ;; dke : DeclKindEnv
  ;; intro-env : Env
  [dke decl -> decl- intro-env]
  [dke ⊢ decl ≫ decl- decl⇒ intro-env]
  [dke ⊢ decl]
  [≫ decl- decl⇒ intro-env]
  #:in-stx decl
  #:out-stx decl-
  #:stop-ids (map first dke)
  #:bad-output (raise-syntax-error #f "expected a type or val declaration" decl))

;; expand value definitions and typecheck their RHS
(define-expand-check-relation tc/val-def
  ;; G : Env
  [G defn -> defn-]
  [G ⊢ defn ≫ defn- val-def⇐]
  [G ⊢ defn]
  [≫ defn-]
  #:in-stx defn
  #:out-stx defn-
  #:stop-ids '()
  #:bad-output (raise-syntax-error #f "expected a type or val declaration" defn))

;; -------------------------------------------------------------------
;; expanding types

(define-expand-check-relation tc/type
  ;; dke : DeclKindEnv
  [dke ty -> ty-]
  [dke ⊢ ty ≫ ty- type⇐]
  [dke ⊢ ty]
  [≫ ty- type⇐]
  #:in-stx ty
  #:out-stx ty-
  #:stop-ids (map first dke)
  #:bad-output (raise-syntax-error #f "expected a type" ty))

;; expand-type/dke : DeclKindEnv Stx -> Type
(define (expand-type/dke dke τ-stx)
  (match-define (type-stx τ) (expand/tc/type-in dke τ-stx))
  τ)

;; -------------------------------------------------------------------
;; signature checking

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
