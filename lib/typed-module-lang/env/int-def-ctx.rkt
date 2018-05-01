#lang racket/base

(provide empty-env
         extend
         lookup
         env->assoc)

(require racket/match)

;; An Env is an InternalDefinitionContext

;; An EnvBinding is an arbitrary compile-time value

;; A Bindings is a [Listof [List Id EnvBinding]]

;; --------------------------------------------------------------

(struct opaque-struct [value])

;; -> Env
(define (empty-env)
  (syntax-local-make-definition-context))

;; Env Bindings -> Env
(define (extend env bindings)
  (define env* (syntax-local-make-definition-context env))
  (for ([entry (in-list bindings)])
    (match-define (list id binding) entry)
    (syntax-local-bind-syntaxes (list id) #`#,(opaque-struct entry) env*))
  env*)

;; Env Id -> EnvBinding
(define (lookup env x)
  (opaque-struct-value
   (syntax-local-value
    (internal-definition-context-introduce env x)
    #f
    env)))

;; --------------------------------------------------------------

(define (env->assoc env)
  (for/list ([x (in-list (internal-definition-context-binding-identifiers env))])
    (list x (lookup env x))))

