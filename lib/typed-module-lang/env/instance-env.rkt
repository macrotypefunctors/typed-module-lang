#lang racket/base

(provide empty-instance-env
         instance-env-current
         instance-env-lookup-bindings
         instance-env-extend
         instance-env-extend-current)
         

(require "label-env.rkt")

;; An InstanceContext is a Label

;; An InstanceBindings is a [Listof [List InstanceBinding Id]]
;; where InstanceBinding is from typed-module-lang/rep/type.rkt

;; An InstanceEnv is a
;;   (instance-env InstanceContext [LabelEnvof InstanceBindings])
;; containing a "current" instance context and a mapping
;; from InstanceContexts to InstanceBindings lists
(struct instance-env [current mapping])

;; Every Datatype, Opaque type, and Class will have an InstanceContext,
;; but type aliases will not.

;; -> InstanceEnv
(define (empty-instance-env)
  (define ctx (fresh-label 'instance-context))
  (instance-env ctx
                (label-env-extend (empty-label-env)
                                  (list (list ctx '())))))

;; InstanceEnv InstanceContext -> InstanceBindings
(define (instance-env-lookup-bindings ienv ictx)
  (label-env-lookup (instance-env-mapping ienv) ictx))

;; InstanceEnv InstanceBindings -> InstanceEnv
(define (instance-env-extend ienv bindings)
  (define new-ctx (fresh-label 'instance-context))
  (instance-env
   new-ctx
   (label-env-extend (instance-env-mapping ienv)
                     (list (list new-ctx bindings)))))

;; InstanceENv InstanceBindings -> InstanceEnv
;; Does it make sense to check for orphan instances here?
;; Or in another function that would be similar?
(define (instance-env-extend-current ienv bindings)
  (define ctx (instance-env-current ienv))
  (define mp (instance-env-mapping ienv))
  (instance-env
   ctx
   (label-env-extend mp
                     (append
                      bindings
                      (label-env-lookup
                       mp
                       ctx)))))

