#lang racket/base

(provide (all-from-out macrotypes-nonstx/type-check)
         (all-defined-out)
         cases)

(require macrotypes-nonstx/expand-check-sugar
         macrotypes-nonstx/type-check)

;; -------------------------------------------------------------------
;; type checking within a mod

;; a DeclKindEnv is a [Listof [List Id DeclKind]]
;; a DeclKind is one of:
;;  - 'type-alias
;;  - 'newtype

;; a TypeEnv is a [Listof [List TypeId Type]]    (a TypeId is an Id)
;; a ValEnv is a [Listof [List ValId Type]]      (a ValId is an Id)

;; which types exist? are they aliases or newtypes?
(define-expand-check-relation tc/type-decl
  ;; intro-decls : DeclKindEnv
  [decl -> decl- intro-decls]
  [⊢ decl ≫ decl- type-decl⇒ intro-decls]
  [⊢ decl]
  [≫ decl- type-decl⇒ intro-decls]
  #:in-stx decl
  #:out-stx decl-
  #:stop-ids '()
  #:bad-output (raise-syntax-error #f "expected a type or val declaration" decl))

;; expand types within type aliases and newtypes
;; TODO: when do we check for recursion in type aliases? what information do we need?
(define-expand-check-relation tc/type-def
  ;; intro-types : TypeEnv
  [decl-kinds defn -> defn- intro-types]
  [decl-kinds ⊢ defn ≫ defn- type-def⇒ intro-types]
  [decl-kinds ⊢ defn]
  [≫ defn- type-def⇒ intro-types]
  #:in-stx defn
  #:out-stx defn-
  #:stop-ids '()
  #:bad-output (raise-syntax-error #f "expected a type or val declaration" defn))

(define-expand-check-relation tc/val-decl
  ;; type-env : TypeEnv
  ;; intro-vals : ValEnv
  [type-env decl -> decl- intro-vals]
  [type-env ⊢ decl ≫ decl- val-decl⇒ intro-vals]
  [type-env ⊢ decl]
  [≫ decl- val-decl⇒ intro-vals]
  #:in-stx decl
  #:out-stx decl-
  #:stop-ids '()
  #:bad-output (raise-syntax-error #f "expected a type or val declaration" decl))

(define-expand-check-relation tc/val-def
  ;; type-env : TypeEnv
  [type-env defn -> defn-]
  [type-env ⊢ defn ≫ defn- val-def⇐]
  [type-env ⊢ defn val-def⇐]
  [≫ defn-]
  #:in-stx defn
  #:out-stx defn-
  #:stop-ids '()
  #:bad-output (raise-syntax-error #f "expected a type or val declaration" defn))

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
