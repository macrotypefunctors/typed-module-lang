#lang racket

(provide env
         env-binding-store
         env-label-env
         empty-env
         lookup
         lookup-label
         extend
         env-ids)

(require "binding-store.rkt"
         "label-env.rkt")

;; An Environment has two parts:
;;  * The BindingStore maps identifiers to unique symbols called "labels"
;;  * The LabelEnv maps the labels to values

;; A Bindings is a [Listof [List Id Label EnvBinding]]

(struct env [binding-store label-env])

(define (lookup-label G x)
  (match-define (env bs le) G)
  (binding-store-lookup bs x))

(define (empty-env)
  (env (empty-binding-store) (empty-label-env)))

(define (lookup G x)
  (match-define (env bs le) G)
  (label-env-lookup le (binding-store-lookup bs x)))

;; Env Bindings -> Env
(define (extend G entries)
  (match-define (env bs le) G)
  (define bs*
    (binding-store-extend
     bs
     (for/list ([ent (in-list entries)])
       (list (first ent) (second ent)))))
  (define le*
    (label-env-extend
     le
     (for/list ([ent (in-list entries)])
       (list (second ent) (third ent)))))
  (env bs* le*))

(define (env-ids G)
  (binding-store-ids (env-binding-store G)))

