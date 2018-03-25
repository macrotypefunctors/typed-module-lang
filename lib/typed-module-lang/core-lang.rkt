#lang racket/base

(provide Int
         ->
         val
         type
         (rename-out [core-lang-module-begin #%module-begin])
         #%datum
         #%var
         (for-syntax core-lang-tc-passes))

(require syntax/parse/define
         macrotypes-nonstx/type-macros
         (for-syntax racket/base
                     racket/match
                     racket/syntax
                     macrotypes-nonstx/type-prop
                     "type-check.rkt"
                     ))

(begin-for-syntax
  ;; the body should return 2 values:
  ;;  - the next value for the acc-id
  ;;  - the element of the result list
  ;; the whole form returns 2 values:
  ;;  - the final value for the acc-id
  ;;  - the whole result list
  ;; for/list/acc does not handle #:break in the body
  (define-syntax-rule (for/list/acc ([acc-id acc-init])
                                    (clause ...)
                        body ...)
    (for/fold ([acc-id acc-init]
               [rev-list-id '()]
               #:result (values acc-id (reverse rev-list-id)))
              (clause ...)
      (let-values ([(acc-new elem-new)
                    (let () body ...)])
        (values acc-new (cons elem-new rev-list-id))))))

;; ----------------------------------------------------

;; a Type is one of
;;   - BaseType
;;   - (-> [Listof Type] Type)
;;   - (named-reference Id)

(define-base-type Int)
(define-type-constructor Arrow [inputs output])

(begin-for-syntax
  (struct named-reference [id])

  ;; Env Type Type -> Boolean
  (define/match (subtype? G τ1 τ2)
    [[_ (Arrow τ1-ins τ1-out) (Arrow τ2-ins τ2-out)]
     (define (<: a b) (subtype? G a b))
     (and (andmap <: τ2-ins τ1-ins)
          (<: τ1-out τ2-out))]

    [[_ (named-reference x) (named-reference y)]
     (or (free-identifier=? x y)
         (match* [(env-lookup-type-decl x)
                  (env-lookup-type-decl y)]
           [[(type-alias-decl τ1*) _] (subtype? G τ1* τ2)]
           [[_ (type-alias-decl τ2*)] (subtype? G τ1 τ2*)]
           [[_ _] #f]))]

    [[_ _ _] (equal? τ1 τ2)])

  ;; Env Type Type -> Boolean
  (define (type≈? τ1 τ2)
    (and (subtype? τ1 τ2)
         (subtype? τ2 τ1)))

  ;; TODO: change implicit ⇐ rule to use subtype?
  )

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
       decl-kinds⇒ (list (list #'X 'type-alias)))]
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

(define-typed-syntax #%datum
  [⊢≫⇒
   [G ⊢ #'(_ . i:exact-integer)]
   (er ⊢≫⇒ ≫ #''i ⇒ (Int))])

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

;; ----------------------------------------------------
