#lang racket/base

(provide (for-syntax core-lang-tc-passes)
         ; types
         Int Bool -> ∀ =>
         ; forms
         val
         type
         newtype
         class
         check
         #%var
         (rename-out
          [core-lang-module-begin #%module-begin]
          [core-lang-datum #%datum]
          [core-lang-app #%app]
          [core-lang-lambda lambda]
          [core-lang-lambda λ]
          [core-lang-let let]
          [core-lang-if if]
          [core-lang-Λ Λ]
          [core-lang-inst inst]
          [core-lang-resolve resolve]
          ;; prim ops
          [core-lang-+ +]
          [core-lang-- -]
          [core-lang-* *]
          [core-lang-quotient quo]
          [core-lang-remainder rem]
          [core-lang-< <]
          [core-lang-> >]
          [core-lang-= =]))

(require syntax/parse/define
         macrotypes-nonstx/type-macros
         rackunit
         racket/function
         (for-syntax racket/base
                     racket/list
                     racket/match
                     racket/pretty
                     racket/syntax
                     macrotypes-nonstx/type-prop
                     macrotypes-nonstx/id-transformer
                     "type-check.rkt"
                     "type.rkt"
                     "env/combined-env.rkt"
                     "env/label-env.rkt"
                     "print/print-type.rkt"
                     "print/print-env.rkt"
                     "util/for-acc.rkt"
                     ))

;; ----------------------------------------------------

(define-for-syntax (prim-type-transformer t)
  (id-transformer (cases [⊢τ≫type⇐ [dke ⊢τ _] (type-stx t)])))

(define-syntax Int (prim-type-transformer (Int)))
(define-syntax Bool (prim-type-transformer (Bool)))

(define-typed-syntax ->
  [⊢τ≫type⇐
   [dke ⊢τ #'(-> in* ... out*)]
   (define (expand-type t) (expand-type/dke dke t))
   (define ins (map expand-type (attribute in*)))
   (define out (expand-type #'out*))
   (type-stx (Arrow ins out))])

(define-typed-syntax ∀
  [⊢τ≫type⇐
   [dke ⊢τ #'(_ (x:id ...) body*:expr)]
   (define body-dke
     (extend dke (map (λ (x) (list x 'type)) (attribute x))))
   (define x-labels (map (λ (x) (lookup-label body-dke x)) (attribute x)))
   (define body (expand-type/dke body-dke #'body*))
   (type-stx (Forall x-labels body))])

(define-typed-syntax =>
  [⊢τ≫type⇐
   [dke ⊢τ #'(_ (class-name:id con*:expr) body*:expr)]
   (define class (label-reference (lookup-label dke #'class-name)))
   (define con  (expand-type/dke dke #'con*))
   (define body (expand-type/dke dke #'body*))
   (type-stx (Qual (constraint class con) body))]

  [⊢e≫⇒
   [G ⊢e #'(_ (class-name:id con-type:expr) body:expr)]
   (define class (label-reference (lookup-label G #'class-name)))
   (define dke G)
   (define τ_con (expand-type/dke dke #'con-type))
   (define dict-id (generate-temporary #'inst))
   (define G+instance
     (extend G (list (list dict-id (instance-binding class τ_con)))))
   (ec G+instance ⊢e #'body ≫ #'body- ⇒ τ_b)
   (er ⊢e≫⇒ ≫ #`(λ (#,dict-id) body-)
       ⇒ (Qual (constraint class τ_con) τ_b))])


;; ----------------------------------------------------

;; A "whole program" for core-lang follows this rule

(begin-for-syntax
  ;; core-lang-tc-passes :
  ;; Env [Listof Stx] -> (values [Listof Stx] Env Bindings)
  ;; Returns 3 values:
  ;;  * expanded-decls : [Listof Stx]
  ;;    A list of the expanded declarations
  ;;  * inside-env     : Env
  ;;    The environment inside the program, determines what the *labels* are
  ;;  * bindings       : Bindings
  ;;    A list of the new bindings introduced by the declarations.
  ;;    The identifiers in the lhs's of these bindings are *reference*
  ;;    positions, which have labels in the binding store of the inside-env.
  (define (core-lang-tc-passes external-G ds)
    ;; pass 1
    ;; the identifiers produced here in the dkel are binding positions
    ;; or "definitions"
    (define-values [dkel ds/1]
      (for/list/acc ([dkel '()])
                    ([d (in-list ds)])
        (ec ⊢ d ≫ d- decl-kinds⇒ dkel+)
        (values (append dkel+ dkel)
                d-)))
    (define dke+external
      ;; note: important that 'dkel' entries are "closer"
      ;;   than entries in 'external-G'
      (extend external-G
              (for/list ([ent (in-list dkel)])
                (match ent
                  [(list k v)
                   (list (syntax-local-introduce k) v)]))))
    ;; pass 2
    ;; the identifiers produced here in the envl are reference positions
    ;; or "uses"
    (define-values [envl ds/2]
      (for/list/acc ([Gl '()])
                    ([d (in-list ds/1)])
        (ec dke+external ⊢ d ≫ d- decl⇒ Gl+)
        (values (append Gl+ Gl)
                d-)))
    (define envl*
      (for/list ([ent (in-list envl)])
        (match ent
          [(list k v)
           (list (syntax-local-introduce k) v)])))
    (define env+external
      ;; note: important that 'envl' entries are "closer"
      ;;   than entries in 'external-G'
      (replace dke+external envl*))
    ;; pass 3
    (define ds/3
      (for/list ([d (in-list ds/2)])
        (ec env+external ⊢ d ≫ d- val-def⇐)
        d-))
    ; note: return just 'envl', not 'env+external' (see purpose statement)
    (values ds/3 env+external envl*)))

(define-syntax core-lang-module-begin
  (syntax-parser
    [(_ d:expr ...)
     (define-values [ds- env bindings]
       (core-lang-tc-passes (empty-env) (attribute d)))
     (print-bindings env bindings)
     #`(#%module-begin #,@ds-)]))

;; ----------------------------------------------------

;; core-def forms:
;;  - val
;;  - type
;;  - newtype

(define-typed-syntax val
  #:datum-literals [: =]
  ;; pass 1
  [⊢≫decl-kinds⇒ [⊢ stx]
   #:with (_ x:id . _) stx
   (er ⊢≫decl-kinds⇒ ≫ stx
       decl-kinds⇒ (list (list (syntax-local-introduce #'x) 'val)))]
  ;; pass 2
  [⊢≫decl⇒
   [dke ⊢ #'(_ x : τ-stx:expr . stuff)]
   ;(ec dke ⊢ #'τ-stx ≫ τ type⇐)
   (define τ (expand-type/dke dke #'τ-stx))
   (er ⊢≫decl⇒
       ≫ (quasisyntax/loc this-syntax
           (val x : #,(type-stx τ) . stuff))
       decl⇒ (list (list (syntax-local-introduce #'x) (val-binding τ))))]
  ;; pass 3
  [⊢≫val-def⇐
   ; this G will include all top-level definitions in the program
   ; e can only be typechecked in *this* G
   [G ⊢ #'(_ x : τ-stx = e:expr)]
   (define τ (expand-type #'τ-stx)) ;; don't need to use env because already expanded
   (ec G ⊢e #'e ≫ #'e- ⇐ τ)
   (er ⊢≫val-def⇐ ≫ #`(define x e-))])

(define-typed-syntax type
  #:datum-literals [: =]
  ;; pass 1
  [⊢≫decl-kinds⇒
   [⊢ #'(_ X:id . stuff)]
   (er ⊢≫decl-kinds⇒
       ≫ (syntax/loc this-syntax
           (type X . stuff))
       decl-kinds⇒ (list (list (syntax-local-introduce #'X) 'type)))]
  ;; pass 2
  [⊢≫decl⇒
   [dke ⊢ #'(_ X = τ-stx)]
   (define τ (expand-type/dke dke #'τ-stx))
   ;; TODO: check for recursion / mutual-recursion somewhere
   (er ⊢≫decl⇒
       ≫ #'(type X = τ-stx)
       decl⇒ (list (list (syntax-local-introduce #'X)
                         (type-binding (type-alias-decl τ)))))]
  ;; pass 3
  [⊢≫val-def⇐
   [_ ⊢ stx]
   (er ⊢≫val-def⇐ ≫ #'(begin))])

(define-typed-syntax newtype
  #:datum-literals [=]
  ;; pass 1
  [⊢≫decl-kinds⇒
   [⊢ #'(_ X:id = (constr:id core-type))]
   (er ⊢≫decl-kinds⇒
       ≫ this-syntax
       decl-kinds⇒ (list (list (syntax-local-introduce #'X) 'type)
                         (list (syntax-local-introduce #'constr) 'val)))]
  ;; pass 2
  [⊢≫decl⇒
   [dke ⊢ #'(_ X:id = (constr:id core-type))]
   (define core-τ (expand-type/dke dke #'core-type))
   (define X-label (lookup-label dke #'X))
   (define constr-label (lookup-label dke #'constr))
   (er ⊢≫decl⇒
       ≫ this-syntax
       decl⇒ (list (list (syntax-local-introduce #'X)
                         (type-binding (data-decl (list constr-label))))
                   (list (syntax-local-introduce #'constr)
                         (constructor-binding
                          (Arrow (list core-τ)
                                 (label-reference X-label))))))]
  ;; pass 3
  [⊢≫val-def⇐
   [_ ⊢ #'(_ X:id = (constr:id core-type))]
   (er ⊢≫val-def⇐ ≫ #'(define constr identity))])

(begin-for-syntax
  (define-syntax-class method-spec
    #:datum-literals [:]
    [pattern [name:id : type:expr]]))

(define-typed-syntax class
  ;; pass 1
  [⊢≫decl-kinds⇒
   [⊢ #'(_ (class-name:id var:id) m:method-spec ...)]
   (er ⊢≫decl-kinds⇒
       ≫ this-syntax
       decl-kinds⇒ (list* (list (syntax-local-introduce #'class-name) 'class)
                          (map (λ (m) (list (syntax-local-introduce m) 'val))
                               (attribute m.name))))]

  ;; pass 2
  [⊢≫decl⇒
   [dke ⊢ #'(_ (class-name:id var:id) m:method-spec ...)]
   (define dke+var (extend dke (list (list #'var 'type))))
   (define var-label (lookup-label dke+var #'var))
   (define class-label (lookup-label dke+var #'class-name))
   (define (expand-type t) (expand-type/dke dke+var t))
   (define methods
     (for/hash ([name (in-list (attribute m.name))]
                [type (in-list (attribute m.type))])
       (values (syntax-e name)
               (expand-type type))))
   (define method-intros
     (for/list ([name (in-list (attribute m.name))])
       (define τ (hash-ref methods (syntax-e name)))
       (define τ-qual
         (Forall (list var-label)
                 (Qual (constraint (label-reference class-label)
                                   (label-reference var-label))
                       τ)))
       (list (syntax-local-introduce name)
             (val-binding τ-qual))))
   (er ⊢≫decl⇒
       ≫ this-syntax
       decl⇒ (list* (list (syntax-local-introduce #'class-name)
                          (typeclass-binding var-label methods))
                    method-intros))]

  ;; pass 3
  [⊢≫val-def⇐
   [G ⊢ #'(_ (class-name:id _) m:method-spec ...)]
   (er ⊢≫val-def⇐ ≫
       #'(begin
           (define (m.name dict)
             (hash-ref dict 'm.name))
           ...))])


(define-for-syntax (prettify/#%dot dat)
  (match dat
    [(list '#%dot x y)
     (format "~a.~a" (prettify/#%dot x) (prettify/#%dot y))]
    [_ (format "~a" (if (list? dat)
                        (map prettify/#%dot dat)
                        dat))]))

(define-typed-syntax check
  #:datum-literals [=]
  ;; pass 1
  [⊢≫decl-kinds⇒ [⊢ stx] (er ⊢≫decl-kinds⇒ ≫ stx decl-kinds⇒ '())]
  ;; pass 2
  [⊢≫decl⇒ [dke ⊢ stx] (er ⊢≫decl⇒ ≫ stx decl⇒ '())]
  ;; pass 3
  [⊢≫val-def⇐
   [G ⊢ #'(_ e1 = e2)]
   #:with msg (format "~a = ~a"
                      (prettify/#%dot (syntax->datum #'e1))
                      (prettify/#%dot (syntax->datum #'e2)))
   (ec G ⊢e #'e1 ≫ #'e1- ⇒ τ)
   (ec G ⊢e #'e2 ≫ #'e2- ⇐ τ)
   (er ⊢≫val-def⇐ ≫ #'(check-equal? e1- e2- 'msg))])

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
  [⊢e≫⇒
   [G ⊢e #'(_ x:id)]
   (match (env-lookup-val G #'x)
     [#f (raise-syntax-error #f "cannot use type as term" #'x)]
     [τ (er ⊢e≫⇒ ≫ #'x ⇒ τ)])]
  ;; as a type
  [⊢τ≫type⇐
   [dke ⊢τ #'(_ x:id)]
   (match (lookup dke #'x)
     [(or 'type (type-binding _))
      ;; don't return er, return type-stx with a *type struct* instead
      (type-stx (label-reference (lookup-label dke #'x)))]
     [_
      (raise-syntax-error #f "expected a type" #'x)])])

(define-typed-syntax core-lang-datum
  [⊢e≫⇒
   [G ⊢e #'(_ . i:exact-integer)]
   (er ⊢e≫⇒ ≫ #''i ⇒ (Int))]
  [⊢e≫⇒
   [G ⊢e #'(_ . {~and b {~or #t #f}})]
   (er ⊢e≫⇒ ≫ #''b ⇒ (Bool))])

(begin-for-syntax
  ;; follows type aliases until a non-alias type is found, and returns it
  ;; Env Type -> Type
  (define (dereference-type G τ)
    (match τ
      [(label-reference x)
       (match (lenv-lookup-type-decl (env-label-env G) x)
         [(type-alias-decl τ*) (dereference-type G τ*)]
         [_ τ])]
      [_ τ]))

  ;; follows type aliases until an Arrow type is found, or raises a syntax
  ;; error on the given syntax if not found
  ;; Stx Env Type -> ArrowType
  (define (find-arrow-type stx G τ)
    (define τ* (dereference-type G τ))
    (if (Arrow? τ*)
        τ*
        (raise-syntax-error #f
          (format "expected function type, got ~a"
                  (type->string G τ))
          stx)))

  ;; like find-arrow-type but looks for Forall types
  ;; Stx Env Type -> ForallType
  (define (find-forall-type stx G τ)
    (define τ* (dereference-type G τ))
    (if (Forall? τ*)
        τ*
        (raise-syntax-error #f
          (format "expected forall type, got ~a"
                  (type->string G τ))
          stx)))

  ;; like find-arrow-type but looks for Qual types
  ;; Stx Env Type -> QualType
  (define (find-qual-type stx G τ)
    (define τ* (dereference-type G τ))
    (if (Qual? τ*)
        τ*
        (raise-syntax-error #f
          (format "expected => type, got ~a"
                  (type->string G τ))
          stx)))

  )

(define-typed-syntax core-lang-lambda
  [⊢e≫⇐
   [G ⊢e #'(_ (x:id ...) body:expr) ⇐ τ_expected]
   (match-define (Arrow τ_as τ_b) (find-arrow-type this-syntax G τ_expected))
   (define body-G
     (extend G
             (map list (attribute x) (map val-binding τ_as))))
   (ec body-G ⊢e #'body ≫ #'body- ⇐ τ_b)
   (er ⊢e≫⇐ ≫ #`(lambda (x ...) body-))]
  [⊢e≫⇒
   [G ⊢e #'(_ ([x:id : τ-stx] ...) body:expr)]
   (define dke G)

   (define (expand-type τ-stx)
     (expand-type/dke dke τ-stx))

   (define τ_xs (map expand-type (attribute τ-stx)))
   (define body-G
     (extend G
             (map list (attribute x) (map val-binding τ_xs))))
   (ec body-G ⊢e #'body ≫ #'body- ⇒ τ_body)
   (er ⊢e≫⇒ ≫ #`(lambda (x ...) body-) ⇒ (Arrow τ_xs τ_body))])

(define-typed-syntax core-lang-app
  ;; as an expression. no type application thus far,
  ;; but the module layer will need to override #%app
  ;; for functor application.
  [⊢e≫⇒
   [G ⊢e #'(_ fn:expr arg:expr ...)]
   (ec G ⊢e #'fn ≫ #'fn- ⇒ τ-fn)
   ;; extract function type
   (match-define (Arrow τ-ins τ-out) (find-arrow-type #'fn G τ-fn))
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
       (ec G ⊢e e ≫ e- ⇐ τ)
       e-))
   (er ⊢e≫⇒ ≫ #`(#%app fn- arg- ...) ⇒ τ-out)])

(define-typed-syntax core-lang-let
  [⊢e≫⇒
   [G ⊢e #'(_ ([x:id e:expr] ...) body:expr)]
   #:do [(define-values [es- τ_xs]
           (for/lists (es- τ_xs)
                      ([e (in-list (attribute e))])
             (ec G ⊢e e ≫ e- ⇒ τ_e)
             (values e- τ_e)))]
   #:with [e- ...] es-
   (define body-G
     (extend G
             (map list (attribute x) (map val-binding τ_xs))))
   (ec body-G ⊢e #'body ≫ #'body- ⇒ τ_b)
   (er ⊢e≫⇒ ≫ #`(let ([x e-] ...) body-) ⇒ τ_b)])

(define-typed-syntax core-lang-if
  [⊢e≫⇐
   [G ⊢e #'(_ que thn els) ⇐ τ]
   (ec G ⊢e #'que ≫ #'que- ⇐ (Bool))
   (ec G ⊢e #'thn ≫ #'thn- ⇐ τ)
   (ec G ⊢e #'els ≫ #'els- ⇐ τ)
   (er ⊢e≫⇐ ≫ #'(if que- thn- els-))]
  [⊢e≫⇒
   [G ⊢e #'(_ que thn els)]
   (ec G ⊢e #'que ≫ #'que- ⇐ (Bool))
   (ec G ⊢e #'thn ≫ #'thn- ⇒ τ)
   (ec G ⊢e #'els ≫ #'els- ⇐ τ)
   (er ⊢e≫⇒ ≫ #'(if que- thn- els-) ⇒ τ)])

(define-typed-syntax core-lang-Λ
  [⊢e≫⇒
   [G ⊢e #'(_ (X:id ...) body:expr)]
   (define body-G
     (extend G
             (for/list ([X (in-list (attribute X))])
               (list X (type-binding (type-opaque-decl))))))
   (define X-labels
     (map (λ (X) (lookup-label body-G X))
          (attribute X)))
   (ec body-G ⊢e #'body ≫ #'body- ⇒ τ_b)
   (er ⊢e≫⇒ ≫ #'body- ⇒ (Forall X-labels τ_b))]

  [⊢e≫⇐
   [G ⊢e #'(_ (X:id ...) body:expr) ⇐ τ_exp]
   (match-define (Forall Y-labels τ_b) (find-forall-type this-syntax G τ_exp))
   (define body-G
     (extend G
             (for/list ([X (in-list (attribute X))])
               (list X (type-binding (type-opaque-decl))))))
   (define X-labels
     (map (λ (X) (lookup-label body-G X))
          (attribute X)))
   (define τ_b*
     (type-substitute-label* τ_b Y-labels X-labels))
   ;; τ_b* has the X-labels
   (ec body-G ⊢e #'body ≫ #'body- ⇐ τ_b*)
   (er ⊢e≫⇐ ≫ #'body-)])

(define-typed-syntax core-lang-inst
  [⊢e≫⇒
   [G ⊢e #'(_ e:expr t_arg:expr ...)]

   (define dke G)
   (define (expand-type τ-stx)
     (expand-type/dke dke τ-stx))
   (define τ_args
     (map expand-type (attribute t_arg)))

   (ec G ⊢e #'e ≫ #'e- ⇒ τ_e)
   (match-define (Forall Xs τ_inside) (find-forall-type #'e G τ_e))
   (unless (= (length Xs) (length τ_args))
     (raise-syntax-error #f
       "wrong number of arguments to forall type"
       this-syntax))

   (define τ (type-substitute* τ_inside Xs τ_args))
   (er ⊢e≫⇒ ≫ #'e- ⇒ τ)])

(begin-for-syntax

  ;; Env Class Type Class Type -> Bool
  (define (instance-matches? G
                             instance-class instance-type
                             class type)
    ;; TODO: use a recur variant?
    (and (class=? G instance-class class)
         (type=? G instance-type type)))

  ;; Env Constraint -> Stx or #f
  (define (lookup-instance G constr)
    (match-define (constraint c τ) constr)
    ;; look for in two places:
    ;;  - env of original definition of class
    ;;  - env of original definition of τ
    (for/or ([x (in-list (env-ids G))])
      (match (lookup G x)
        [(instance-binding inst-c inst-τ)
         ;; TODO: implement chained instances?
         (and (instance-matches? G inst-c inst-τ c τ)
              x)]
        [_ #f]))))

(define-typed-syntax core-lang-resolve
  [⊢e≫⇒
   [G ⊢e #'(_ e:expr)]
   (ec G ⊢e #'e ≫ #'e- ⇒ τ_e)
   (match-define (Qual constr τ_inside) (find-qual-type #'e G τ_e))
   (match (lookup-instance G constr)
     [#f (raise-syntax-error #f
           (format "cannot resolve instance ~a"
                   (constraint->string G constr))
           #'e)]
     [(? identifier? inst-id)
      (er ⊢e≫⇒ ≫ #`(#%app e- #,inst-id) ⇒ τ_inside)])])

;; ---------------------------------------------------------

(define-for-syntax (typed-prim-transformer internal type)
  (var-like-transformer
   (cases
    [⊢e≫⇒
     [G ⊢e _]
     (er ⊢e≫⇒ ≫ internal ⇒ type)])))

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
  [+ - * quotient remainder]
  (Arrow (list (Int) (Int)) (Int)))

(define-typed-prim
  [< > =]
  (Arrow (list (Int) (Int)) (Bool)))
