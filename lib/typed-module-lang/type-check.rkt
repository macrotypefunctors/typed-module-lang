#lang racket/base

(provide (all-defined-out)
         cases
         ec
         er
         ⊢ ≫ ⇐ ⇒)

(require racket/list
         racket/match
         macrotypes-nonstx/expand-check-sugar
         macrotypes-nonstx/type-prop
         macrotypes-nonstx/type-check
         "type.rkt"
         "sig.rkt"
         "env/assoc.rkt"
         "print/print-type.rkt")

;; -------------------------------------------------------------------

;; Expanding module definitions as submodules within a larger module.

;; pass 0 of mod-body-tc-passes
(define-expand-check-relation sc/def/submod
  [external-G module-def -> module-def- intro-env]
  [external-G ⊢md module-def ≫ module-def- submoddef⇒ intro-env]
  [external-G ⊢md module-def]
  [≫ module-def- submoddef⇒ intro-env]
  #:in-stx module-def
  #:out-stx module-def-
  #:stop-ids '()
  #:bad-output
  (raise-syntax-error #f "expected a typed module definition" module-def))

;; -------------------------------------------------------------------
;; type checking within a mod

;; pass 1 of mod-body-tc-passes and core-lang-tc-passes

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
  #:bad-output (raise-syntax-error #f "expected a type or val declaration" decl)
  #:implicit-rule
  [⊢md≫submoddef⇒
   [G ⊢md stx]
   (er ⊢md≫submoddef⇒ ≫ stx submoddef⇒ '())])

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
  #:stop-ids (map first (env->assoc dke))
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

;; typechecking expressions within a mod
(define-expand-check-relation tc/chk
  ;; G : Env
  [G expr type -> expr-]
  [G ⊢e expr ≫ expr- ⇐ type]
  [G ⊢e expr ⇐ type]
  [≫ expr-]
  #:in-stx expr
  #:out-stx expr-
  #:stop-ids (map first (env->assoc G))
  #:bad-output (raise-syntax-error #f "expected a typed expression" expr))

(define-expand-check-relation tc
  ;; G : Env
  [G expr -> expr- type]
  [G ⊢e expr ≫ expr- ⇒ type]
  [G ⊢e expr]
  [≫ expr- ⇒ type]
  #:in-stx expr
  #:out-stx expr-
  #:stop-ids (map first (env->assoc G))
  #:bad-output (raise-syntax-error #f "expected a typed expression" expr)
  #:implicit-rule
  [⊢e≫⇐
   [G ⊢e expr ⇐ τ-expected]
   (ec G ⊢e expr ≫ expr- ⇒ τ-actual)
   (unless (type-matches? G τ-actual τ-expected)
     (raise-syntax-error #f
       (format "type mismatch\n  expected: ~a\n  given:    ~a"
               (type->string τ-expected)
               (type->string τ-actual))
       expr))
   (er ⊢e≫⇐ ≫ expr-)])

;; -------------------------------------------------------------------
;; expanding types

(define-expand-check-relation tc/type
  ;; dke : DeclKindEnv
  [dke ty -> ty-]
  [dke ⊢τ ty ≫ ty- type⇐]
  [dke ⊢τ ty]
  [≫ ty- type⇐]
  #:in-stx ty
  #:out-stx ty-
  #:stop-ids (map first (env->assoc dke))
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
  [external-G ⊢m module-expr ≫ module-expr- sig⇒ signature-expr]
  [external-G ⊢m module-expr]
  [≫ module-expr- sig⇒ signature-expr]
  #:in-stx module-expr
  #:out-stx module-expr-
  #:stop-ids (map first (env->assoc external-G))
  #:bad-output
  (raise-syntax-error #f "expected a typed module expression" module-expr))

(define-expand-check-relation sc/sig
  [external-G signature-expr -> signature-expr-]
  [external-G ⊢s signature-expr ≫ signature-expr- signature⇐]
  [external-G ⊢s signature-expr]
  [≫ signature-expr- signature⇐]
  #:in-stx signature-expr
  #:out-stx signature-expr-
  #:stop-ids (map first (env->assoc external-G))
  #:bad-output (raise-syntax-error #f "expected a signature" signature-expr))

;; Env Stx -> Signature
(define (expand-signature G signature-stx)
  (match-define (type-stx s) (expand/sc/sig-in G signature-stx))
  s)

;; -------------------------------------------------------------------

;; Expanding Module and Signature Definitions at the *top level*.

;; This is used by mod-lang's #%module-begin

(define-expand-check-relation sc/def/top
  [external-G module-def -> module-def- intro-env]
  [external-G ⊢md module-def ≫ module-def- modsigdef⇒ intro-env]
  [external-G ⊢md module-def]
  [≫ module-def- modsigdef⇒ intro-env]
  #:in-stx module-def
  #:out-stx module-def-
  #:stop-ids '()
  #:bad-output
  (raise-syntax-error #f "expected a typed module definition" module-def))

;; -------------------------------------------------------------------

;; Expanding module definitions either at the top level or as a
;; submodule.

(define-expand-check-relation sc/moddef
  [external-G module-def -> module-def- intro-env]
  [external-G ⊢md module-def ≫ module-def- moddef⇒ intro-env]
  [external-G ⊢md module-def]
  [≫ module-def- moddef⇒ intro-env]
  #:in-stx module-def
  #:out-stx module-def-
  #:stop-ids '()
  #:bad-output
  (raise-syntax-error #f "expected a typed module definition" module-def)
  #:implicit-rule
  [⊢md≫modsigdef⇒
   [G ⊢md module-def]
   (ec G ⊢md module-def ≫ module-def- moddef⇒ intro-env)
   (er ⊢md≫modsigdef⇒ ≫ module-def- modsigdef⇒ intro-env)]
  #:implicit-rule
  [⊢md≫submoddef⇒
   [G ⊢md module-def]
   (ec G ⊢md module-def ≫ module-def- moddef⇒ intro-env)
   (er ⊢md≫submoddef⇒ ≫ module-def- submoddef⇒ intro-env)]
  )

;; implicit rules:
;;
;;   G ⊢md module-def ≫ module-def- moddef⇒ intro-env
;;   --------------------------------------------------
;;   G ⊢md module-def ≫ module-def- modsigdef⇒ intro-env
;;
;;   G ⊢md module-def ≫ module-def- moddef⇒ intro-env
;;   --------------------------------------------------
;;   G ⊢md module-def ≫ module-def- submoddef⇒ intro-env

