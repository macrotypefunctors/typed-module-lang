#lang racket/base

(provide empty-env
         extend
         lookup
         env-ids)

(require racket/list
         racket/match)

;; An Env is one of:
;;  - InternalDefinitionContext
;;  - [Listof InternalDefinitionContext]

;; An EnvBinding is an arbitrary compile-time value

;; A Bindings is a [Listof [List Id EnvBinding]]

;; --------------------------------------------------------------

;; Extending Internal Definition Contexts

;; Adapted from Alexis King's blog post:
;;   Reimplementing Hackett’s type language:
;;   expanding to custom core forms in Racket
;;   https://lexi-lambda.github.io/blog/2018/04/15/
;;   reimplementing-hackett-s-type-language-expanding-
;;   to-custom-core-forms-in-racket/
(define (internal-definition-context-extend old-ctx)
  (match old-ctx
    ['()
     (list (syntax-local-make-definition-context))]
    [(cons fst _)
     (cons (syntax-local-make-definition-context fst) old-ctx)]
    [_
     (list (syntax-local-make-definition-context old-ctx) old-ctx)]))

(define (syntax-local-bind-syntaxes* ids expr-stx ctx)
  (match ctx
    ['() (error "expected an internal definition context")]
    [(cons fst _)
     (syntax-local-bind-syntaxes ids expr-stx fst)]
    [_
     (syntax-local-bind-syntaxes ids expr-stx ctx)]))

(define (internal-definition-context-introduce* ctx stx [mode 'flip])
  (match ctx
    [(list ctxs ...)
     (for/fold ([stx stx]) ([ctx (in-list ctxs)])
       (internal-definition-context-introduce ctx stx mode))]))

;; --------------------------------------------------------------

(struct opaque-struct [value])

;; -> Env
(define (empty-env)
  '())

;; Env Bindings -> Env
(define (extend env bindings)
  (define env* (internal-definition-context-extend env))
  (for ([entry (in-list bindings)])
    (match-define (list id binding) entry)
    (define id* (internal-definition-context-introduce* env* id 'add))
    (syntax-local-bind-syntaxes* (list id*) #`#,(opaque-struct binding) env*))
  env*)

;; Env Id -> EnvBinding
(define (lookup env x)
  (opaque-struct-value
   (syntax-local-value
    (internal-definition-context-introduce* env x 'add)
    #f
    (match env ; for backwards compatibility
      ['() #f]
      [(cons ctx _) env]
      [ctx ctx]))))

;; Env -> [Listof Id]
(define (env-ids env)
  (for*/list ([ctx (in-list env)]
              [id (internal-definition-context-binding-identifiers ctx)])
    (internal-definition-context-introduce* env id 'remove)))

