#lang racket/base

(provide Int
         ->
         val
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
                     "type-check.rkt"))

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

(define-base-type Int)
(define-type-constructor Arrow [inputs output])

(define-syntax-parser ->
  [(-> in* ... out*)
   (define ins (map expand-type (attribute in*)))
   (define out (expand-type #'out*))
   (type-stx (Arrow ins out))])

;; ----------------------------------------------------

;; A "whole program" for core-lang follows this rule

(begin-for-syntax
  ;; core-lang-tc-passes :
  ;; [Listof Stx] -> (values [Listof Stx] TypeEnv ValEnv)
  (define (core-lang-tc-passes ds)
    ;; pass 1
    (define-values [decl-kind-env ds/1]
      (for/list/acc ([dke '()])
                    ([d (in-list ds)])
        (ec ⊢ d ≫ d- type-decl⇒ d-decls)
        (values (append d-decls dke)
                d-)))
    ;; pass 2
    (define-values [type-env ds/2]
      (for/list/acc ([te '()])
                    ([d (in-list ds/1)])
        (ec decl-kind-env ⊢ d ≫ d- type-def⇒ d-types)
        (values (append d-types te)
                d-)))
    ;; pass 3
    (define-values [val-env ds/3]
      (for/list/acc ([G '()])
                    ([d (in-list ds/2)])
        (ec G ⊢ d ≫ d- val-decl⇒ d-vals)
        (values (append d-vals G)
                d-)))
    ;; pass 4
    (define ds/4
      (for/list ([d (in-list ds/3)])
        (ec val-env ⊢ d ≫ d- val-def⇐)
        d-))
    (values ds/4 type-env val-env)))

(define-syntax core-lang-module-begin
  (syntax-parser
    [(_ d:expr ...)
     (define-values [ds- te ve]
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
  [⊢≫type-decl⇒ [⊢ stx] (er ⊢≫type-decl⇒ ≫ stx type-decl⇒ '())]
  ;; pass 2
  [⊢≫type-def⇒ [_ ⊢ stx] (er ⊢≫type-def⇒ ≫ stx type-def⇒ '())]
  ;; pass 3
  [⊢≫val-decl⇒
   [type-env ⊢ #'(_ x:id : τ-stx:expr = e:expr)]
   ;; TODO: use the type-env somehow when processing τ-stx or τ
   (define τ (expand-type #'τ-stx))
   (er ⊢≫val-decl⇒
       ≫ #`(val/pass-4 x : #,(type-stx τ) = e)
       val-decl⇒ (list (list #'x τ)))])

(define-typed-syntax val/pass-4
  #:datum-literals [: =]
  ;; pass 4
  [⊢≫val-def⇐
   ; this G will include all top-level definitions in the program
   ; e can only be typechecked in *this* G
   [G ⊢ #'(_ x : τ-stx = e)]
   (define τ (expand-type #'τ-stx))
   (ec G ⊢ #'e ≫ #'e- ⇐ τ)
   (er ⊢≫val-def⇐
       ≫ #`(define x e-))])

(define-typed-syntax type
  #:datum-literals [: =]
  ;; pass 1
  [⊢≫type-decl⇒
   [⊢ #'(_ name:id . stuff)]
   (er ⊢≫type-decl⇒ ≫ #'(type name . stuff)
       type-decl⇒ (list (list #'name 'type-alias)))]
  ;; pass 2
  [⊢≫type-def⇒
   [decl-kind-env ⊢ #'(_ name:id = τ-stx)]
   ;; TODO: use the decl-kind-env somehow when processing τ-stx or τ
   (define τ (expand-type #'τ-stx))
   (er ⊢≫type-def⇒ ≫ #'(type/pass-3-4) type-def⇒ (list (list #'name τ)))])

(define-typed-syntax type/pass-3-4
  ;; pass 3
  [⊢≫val-decl⇒ [_ ⊢ stx] (er ⊢≫val-decl⇒ ≫ stx val-decl⇒ '())]
  ;; pass 4
  [⊢≫val-def⇐ [_ ⊢ stx] (er ⊢≫val-def⇐ ≫ #'(begin))])

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

