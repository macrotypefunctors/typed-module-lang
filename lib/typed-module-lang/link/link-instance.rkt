#lang racket/base

(require racket/list
         racket/match
         "../rep/type.rkt")

;; This is a "Link-time" module

;; An InstanceContext is a
;;   (Boxof InstanceMapping)
(define BASE-INSTANCE-CONTEXT (box-immutable '()))

;; An InstanceMapping is a
;;   [Listof InstanceEntry]

;; An InstanceEntry is one of:
;;  - [List Constraint InstanceDict]
;; TODO: include "qualified" constraints from instance chaining,
;;       which have "dictionary functions" from instance chaining

;; A Constraint is a (constraint Class Tag)

;; A Class is a:
;;  - (class Label InstanceContext)
(struct class [label instance-context])

;; A Tag is one of:
;;  - 'Int
;;  - 'Bool
;;  - 'Arrow
;;  - (data Label InstanceContext)
(struct data [label instance-context])

;; Class Class -> Bool
(define class=? equal?)

;; Tag Tag -> Bool
(define tag=? equal?)

;; InstanceEntry -> Constraint
;; this will get slightly more complicated with "qualified" constraints,
;; but for now it's this simple
(define instance-entry-result-constraint first)

;; -------------------------------------

;; for every type there is a tag, and
;; for every tag there is an InstanceMapping
;; tag-instance-mapping : Tag -> InstanceMapping
(define (tag-instance-mapping tag)
  (match tag
    [(or 'Int 'Bool 'Arrow) BASE-INSTANCE-CONTEXT]
    [(data label ctx) (unbox ctx)]))

;; for every class there is an InstanceMapping
;; class-instance-mapping : Class -> InstanceMapping
(define (class-instance-mapping c)
  (match c
    [(class label ctx) (unbox ctx)]))

;; -------------------------------------

#|
; (class (Cond X) [test : (-> X Bool)])
; (instance (forall (X) (Cond X) => (Cond (-> X)))
;   ...)

; at LT:  (lookup-instance (Cond (-> Int)))
|#

;; looking up an instance for a constraint looks in two places:
;;  - the type's instance context
;;  - the class's instance context
;; would be called in the "prolog" of a functor as it sets up
;; the "local" instances from the functor argument.
;; It should never fail because Typechecking has already passed.
;; That means the constraint should be guaranteed to be valid.
;; lookup-instance : Constraint -> InstanceDict
(define (lookup-instance con)
  (match-define (constraint class tag) con)
  (define c-ctx (class-instance-mapping class))
  (define t-ctx (tag-instance-mapping tag))
  (define ent
    (or
     (lookup-instance-entry/context con c-ctx)
     (lookup-instance-entry/context con t-ctx)
     (error 'lookup-instance "should never fail")))
  (if (constraint? (first ent))
      (second ent)
      (error 'lookup-instance
             "TODO: solve \"subgoals\" for instance chaining")))

;; lookup-instance-entry/context : Constraint InstanceMapping -> [Maybe InstanceEntry]
(define (lookup-instance-entry/context con ctx)
  (match-define (constraint class type) con)
  (for/or ([ent (in-list ctx)])
    (define ent-con (instance-entry-result-constraint ent))
    (and (constraint-matches? ent-con con)
         ent)))

;; constraint-matches? : Constraint Constraint -> Bool
(define (constraint-matches? con1 con2)
  (match-define (constraint class1 tag1) con1)
  (match-define (constraint class2 tag2) con2)
  (and (class=? class1 class2)
       (tag=? tag1 tag2)))


