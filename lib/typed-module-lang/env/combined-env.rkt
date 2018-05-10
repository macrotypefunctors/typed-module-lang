#lang racket

(provide env
         env-binding-store
         env-label-env
         env-name-env
         empty-env
         lookup
         lookup-label
         extend
         replace
         env-ids
         current-instance-context
         lookup-instance-bindings
         extend-current-instance-context
         )

(require "binding-store.rkt"
         "label-env.rkt"
         "instance-env.rkt")

;; An Environment has four parts:
;;  * The BindingStore maps identifiers to unique symbols called "labels"
;;  * The LabelEnv maps the labels to values
;;  * The NameEnv maps the labels to symbols representing names
;;  * The InstanceEnv keeps track of instances and instance contexts

;; A Bindings is a [Listof [List Id EnvBinding]]

;; A InstanceBindings is a [Listof [List InstanceBinding Id]]

(struct env [binding-store label-env name-env instance-env])

(define (lookup-label G x)
  (match-define (env bs le ne ie) G)
  (binding-store-lookup bs x))

(define (empty-env)
  (env (empty-binding-store) (empty-label-env) (empty-label-env)
       (empty-instance-env)))

(define (lookup G x)
  (match-define (env bs le ne ie) G)
  (label-env-lookup le (binding-store-lookup bs x)))

;; Env Bindings -> Env
;; The identifiers in these bindings are considered binding positions,
;; or "definitions".
;; Maps the identifiers to new labels in the binding store, and maps
;; those labels to the values in the label-env
;; Also: creates a new InstanceContext
(define (extend G entries)
  (match-define (env bs le ne ie) G)
  (define labels (map (compose fresh-label first) entries))
  (define bs*
    (binding-store-extend
     bs
     (for/list ([ent (in-list entries)]
                [lab (in-list labels)])
       (match-define (list id _) ent)
       (list id lab))))
  (define le*
    (label-env-extend
     le
     (for/list ([ent (in-list entries)]
                [lab (in-list labels)])
       (match-define (list _ val) ent)
       (list lab val))))
  (define ne*
    (label-env-extend
     ne
     (for/list ([ent (in-list entries)]
                [lab (in-list labels)])
       (match-define (list id _) ent)
       (list lab (syntax-e id)))))
  (define ie*
    (instance-env-extend ie '()))
  (env bs* le* ne* ie*))

;; Env Bindings -> Env
;; The identifiers in these bindings are considered reference positions,
;; or "uses".
;; Replaces the entries in the label-env, using the existing labels already in
;; the binding store
(define (replace G entries)
  (match-define (env bs le ne ie) G)
  (define le*
    (label-env-extend
     le
     (for/list ([ent (in-list entries)])
       (match-define (list id val) ent)
       (define label (binding-store-lookup bs id))
       (list label val))))
  (env bs le* ne ie))

(define (env-ids G)
  (binding-store-ids (env-binding-store G)))

;; ---------------------------
;; Instances and Instance Contexts

;; Env -> InstanceContext
(define (current-instance-context G)
  (match-define (env bs le ne ie) G)
  (instance-env-current ie))

;; Env InstanceContext -> InstanceBindings
(define (lookup-instance-bindings G ictx)
  (match-define (env bs le ne ie) G)
  (instance-env-lookup-bindings ie ictx))

;; Env InstanceBindings -> Env
(define (extend-current-instance-context G entries)
  (match-define (env bs le ne ie) G)
  (define ie*
    (instance-env-extend-current ie entries))
  (env bs le ne ie*))

