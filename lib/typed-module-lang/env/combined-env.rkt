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
         env-ids)

(require "binding-store.rkt"
         "label-env.rkt")

;; An Environment has two parts:
;;  * The BindingStore maps identifiers to unique symbols called "labels"
;;  * The LabelEnv maps the labels to values
;;  * The NameEnv maps the labels to symbols representing names

;; A Bindings is a [Listof [List Id EnvBinding]]

(struct env [binding-store label-env name-env])

(define (lookup-label G x)
  (match-define (env bs le ne) G)
  (binding-store-lookup bs x))

(define (empty-env)
  (env (empty-binding-store) (empty-label-env) (empty-label-env)))

(define (lookup G x)
  (match-define (env bs le ne) G)
  (label-env-lookup le (binding-store-lookup bs x)))

;; Env Bindings -> Env
;; The identifiers in these bindings are considered binding positions,
;; or "definitions".
;; Maps the identifiers to new labels in the binding store, and maps
;; those labels to the values in the label-env
(define (extend G entries)
  (match-define (env bs le ne) G)
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
  (env bs* le* ne*))

;; Env Bindings -> Env
;; The identifiers in these bindings are considered reference positions,
;; or "uses".
;; Replaces the entries in the label-env, using the existing labels already in
;; the binding store
(define (replace G entries)
  (match-define (env bs le ne) G)
  (define le*
    (label-env-extend
     le
     (for/list ([ent (in-list entries)])
       (match-define (list id val) ent)
       (define label (binding-store-lookup bs id))
       (list label val))))
  (env bs le* ne))

(define (env-ids G)
  (binding-store-ids (env-binding-store G)))

