#lang racket/base

(provide empty-env
         extend
         lookup
         env->assoc)

(require racket/match)

;; An Env is a [Listof [List Id EnvBinding]]

;; An EnvBinding is an arbitrary compile-time value

;; A Bindings is a [Listof [List Id EnvBinding]]

;; --------------------------------------------------------------

;; -> Env
(define (empty-env)
  '())

;; Env Bindings -> Env
(define (extend env bindings)
  (for/fold ([env* env])
            ([entry (in-list bindings)])
    (cons entry env*)))

;; Env Id -> EnvBinding
(define (lookup env x)
  (match (assoc x env free-identifier=?)
    [(list _ v) v]
    [#f (raise-syntax-error #f "binding not found" x)]))

;; --------------------------------------------------------------

(define (env->assoc env) env)

