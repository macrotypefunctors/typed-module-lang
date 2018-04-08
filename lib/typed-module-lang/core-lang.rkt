#lang racket/base

(provide (for-syntax core-lang-tc-passes)
         ; types
         Int ->
         ; forms
         val
         type
         #%var
         (rename-out
          [core-lang-module-begin #%module-begin]
          [core-lang-datum #%datum]
          [core-lang-app #%app]
          [core-lang-lambda lambda]
          [core-lang-lambda λ]
          [core-lang-let let]
          ;; prim ops
          [core-lang-+ +]
          [core-lang-- -]
          [core-lang-* *]
          [core-lang-/ /]))

(require syntax/parse/define
         macrotypes-nonstx/type-macros
         (for-syntax racket/base
                     racket/list
                     racket/match
                     racket/pretty
                     racket/syntax
                     macrotypes-nonstx/type-prop
                     macrotypes-nonstx/id-transformer
                     "type-check.rkt"
                     "type.rkt"
                     "util/for-acc.rkt"
                     ))

;; ----------------------------------------------------

(define-syntax Int
  (id-transformer
   (cases
    [⊢≫type⇐
     [dke ⊢ _]
     (type-stx (Int))])))

(define-typed-syntax ->
  [⊢≫type⇐
   [dke ⊢ #'(-> in* ... out*)]
   (define (expand-type t) (expand-type/dke dke t))
   (define ins (map expand-type (attribute in*)))
   (define out (expand-type #'out*))
   (type-stx (Arrow ins out))])

;; ----------------------------------------------------

;; A "whole program" for core-lang follows this rule

(begin-for-syntax
  ;; core-lang-tc-passes :
  ;; [Listof Stx] -> (values [Listof Stx] Env)
  (define (core-lang-tc-passes ds)
    ;; pass 1
    (define-values [decl-kind-env ds/1]
      (for/list/acc ([dke '()])
                    ([d (in-list ds)])
        (ec ⊢ d ≫ d- decl-kinds⇒ dke+)
        (values (append dke+ dke)
                d-)))
    ;; pass 2
    (define-values [env ds/2]
      (for/list/acc ([G '()])
                    ([d (in-list ds/1)])
        (ec decl-kind-env ⊢ d ≫ d- decl⇒ G+)
        (values (append G+ G)
                d-)))
    ;; pass 3
    (define ds/3
      (for/list ([d (in-list ds/2)])
        (ec env ⊢ d ≫ d- val-def⇐)
        d-))
    (values ds/3 env)))

(define-syntax core-lang-module-begin
  (syntax-parser
    [(_ d:expr ...)
     (define-values [ds- G]
       (core-lang-tc-passes (attribute d)))
     (pretty-print G)
     #`(#%module-begin #,@ds-)]))

;; ----------------------------------------------------

;; core-def forms:
;;  - val
;;  - type
;;  - newtype

(define-typed-syntax val
  #:datum-literals [: =]
  ;; pass 1
  [⊢≫decl-kinds⇒ [⊢ stx] (er ⊢≫decl-kinds⇒ ≫ stx decl-kinds⇒ '())]
  ;; pass 2
  [⊢≫decl⇒
   [dke ⊢ #'(_ x : τ-stx . stuff)]
   ;(ec dke ⊢ #'τ-stx ≫ τ type⇐)
   (define τ (expand-type/dke dke #'τ-stx))
   (er ⊢≫decl⇒
       ≫ #`(val x : #,(type-stx τ) . stuff)
       decl⇒ (list (list #'x (val-binding τ))))]
  ;; pass 3
  [⊢≫val-def⇐
   ; this G will include all top-level definitions in the program
   ; e can only be typechecked in *this* G
   [G ⊢ #'(_ x : τ-stx = e)]
   (define τ (expand-type #'τ-stx)) ;; don't need to use env because already expanded
   (ec G ⊢ #'e ≫ #'e- ⇐ τ)
   (er ⊢≫val-def⇐ ≫ #`(define x e-))])

(define-typed-syntax type
  #:datum-literals [: =]
  ;; pass 1
  [⊢≫decl-kinds⇒
   [⊢ #'(_ X:id . stuff)]
   (er ⊢≫decl-kinds⇒
       ≫ #'(type X . stuff)
       decl-kinds⇒ (list #'X))]
  ;; pass 2
  [⊢≫decl⇒
   [dke ⊢ #'(_ X = τ-stx)]
   (define τ (expand-type/dke dke #'τ-stx))
   ;; TODO: check for recursion / mutual-recursion somewhere
   (er ⊢≫decl⇒
       ≫ #'(type X = τ-stx)
       decl⇒ (list (list #'X (type-binding (type-alias-decl τ)))))]
  ;; pass 3
  [⊢≫val-def⇐
   [_ ⊢ stx]
   (er ⊢≫val-def⇐ ≫ #'(begin))])

;; ----------------------------------------------------

;; core-expr forms:
;;  - #%datum
;;  - #%app
;;  - λ
;;  - #%var
;;  - Λ
;;  - inst

;; for now, no `inst` type inference

(define-typed-syntax #%var
  ;; as an expression
  [⊢≫⇒
   [G ⊢ #'(_ x:id)]
   (match (env-lookup-val G #'x)
     [#f (raise-syntax-error #f "cannot use type as term" #'x)]
     [τ (er ⊢≫⇒ ≫ #'x ⇒ τ)])]
  ;; as a type
  [⊢≫type⇐
   [dke ⊢ #'(_ x:id)]
   ;; don't return er, return type-stx with a *type struct* instead
   ;; TODO: think more about whether this `named-referenced` thing
   ;;       should use an identifier or a symbol, or whether it should
   ;;       use something else entirely
   (type-stx (named-reference #'x))])

(define-typed-syntax core-lang-datum
  [⊢≫⇒
   [G ⊢ #'(_ . i:exact-integer)]
   (er ⊢≫⇒ ≫ #''i ⇒ (Int))])

(begin-for-syntax
  ;; traverses type aliases until an Arrow type is found.
  ;; Env Type -> Arrow or #f
  (define (find-arrow-type G τ)
    (match τ
      [(Arrow _ _) τ]
      [(named-reference x)
       (match (env-lookup-type-decl G x)
         [(type-alias-decl τ*) (find-arrow-type G τ*)]
         [_ #f])]
      [_ #f])))

(define-typed-syntax core-lang-lambda
  [⊢≫⇐
   [G ⊢ #'(_ (x:id ...) body:expr) ⇐ τ_expected]
   (match-define (Arrow τ_as τ_b) (find-arrow-type G τ_expected))
   (define body-G
     (append (map list (attribute x) (map val-binding τ_as))
             G))
   (ec body-G ⊢ #'body ≫ #'body- ⇐ τ_b)
   (er ⊢≫⇐ ≫ #`(lambda (x ...) body-))]
  [⊢≫⇒
   [G ⊢ #'(_ ([x:id : τ-stx] ...) body:expr)]
   (define dke
     (for/list ([entry (in-list G)]
                #:when (type-binding? (second entry)))
       (first entry)))
   (define (expand-type τ-stx)
     (expand-type/dke dke τ-stx))
   (define τ_xs (map expand-type (attribute τ-stx)))
   (define body-G
     (append (map list (attribute x) (map val-binding τ_xs))
             G))
   (ec body-G ⊢ #'body ≫ #'body- ⇒ τ_body)
   (er ⊢≫⇒ ≫ #`(lambda (x ...) body-) ⇒ (Arrow τ_xs τ_body))])

(define-typed-syntax core-lang-app
  ;; as an expression. no type application thus far,
  ;; but the module layer will need to override #%app
  ;; for functor application.
  [⊢≫⇒
   [G ⊢ #'(_ fn:expr arg:expr ...)]
   (ec G ⊢ #'fn ≫ #'fn- ⇒ τ-fn)
   ;; extract function type
   (define-values [τ-ins τ-out]
     (match (find-arrow-type G τ-fn)
       [(Arrow i o) (values i o)]
       [_ (raise-syntax-error #f
            (format "cannot apply non-function type ~a" τ-fn)
            this-syntax)]))
   ;; compare # of arguments
   (unless (= (length τ-ins) (length (attribute arg)))
     (raise-syntax-error #f
       (format "wrong number of argument to function, expected ~a, got ~a"
               (length τ-ins)
               (length (attribute arg)))
       this-syntax))
   ;; typecheck arguments
   (define/syntax-parse (arg- ...)
     (for/list ([τ (in-list τ-ins)]
                [e (in-list (attribute arg))])
       (ec G ⊢ e ≫ e- ⇐ τ)
       e-))
   (er ⊢≫⇒ ≫ #`(#%app fn- arg- ...) ⇒ τ-out)])

(define-typed-syntax core-lang-let
  [⊢≫⇒
   [G ⊢ #'(_ ([x:id e:expr] ...) body:expr)]
   #:do [(define-values [es- τ_xs]
           (for/lists (es- τ_xs)
                      ([e (in-list (attribute e))])
             (ec G ⊢ e ≫ e- ⇒ τ_e)
             (values e- τ_e)))]
   #:with [e- ...] es-
   (define body-G
     (append (map list (attribute x) (map val-binding τ_xs))
             G))
   (ec body-G ⊢ #'body ≫ #'body- ⇒ τ_b)
   (er ⊢≫⇒ ≫ #`(let ([x e-] ...) body-) ⇒ τ_b)])

;; ---------------------------------------------------------

(define-for-syntax (typed-prim-transformer internal type)
  (var-like-transformer
   (cases
    [⊢≫⇒
     [G ⊢ _]
     (er ⊢≫⇒ ≫ internal ⇒ type)])))

(define-syntax define-typed-prim
  (syntax-parser
    [(_ X:id ty)
     #:with core-lang-X (format-id #'X "core-lang-~a" #'X)
     #'(define-syntax core-lang-X
         (typed-prim-transformer #'X ty))]

    [(_ [X:id ...] ty)
     #'(begin
         (define-typed-prim X ty) ...)]))

(define-typed-prim
  [+ - * /]
  (Arrow (list (Int) (Int)) (Int)))
