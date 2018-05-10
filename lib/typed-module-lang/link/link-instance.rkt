#lang racket/base

(require racket/list
         racket/match
         "../rep/type.rkt")

;; This is a "Link-time" module

;; An InstanceContext is a
;;   [Listof InstanceEntry]

;; An InstanceEntry is one of:
;;  - [List Constraint InstanceDict]
;; TODO: include "qualified" constraints from instance chaining,
;;       which have "dictionary functions" from instance chaining

;; InstanceEntry -> Constraint
;; this will get slightly more complicated with "qualified" constraints,
;; but for now it's this simple
(define instance-entry-result-constraint first)

;; -------------------------------------

;; for every type there is an InstanceContext
;; type-instance-context : Type -> InstanceContext
(define (type-instance-context type)
  ('....))

;; for every class there is an InstanceContext
;; class-instance-context : Class -> InstanceContext
(define (class-instance-context class)
  ('....))

;; -------------------------------------

;; looking up an instance for a constraint looks in two places:
;;  - the type's instance context
;;  - the class's instance context
;; would be called in the "prolog" of a functor as it sets up
;; the "local" instances from the functor argument.
;; It should never fail because Typechecking has already passed.
;; That means the constraint should be guaranteed to be valid.
;; lookup-instance : Constraint -> InstanceDict
(define (lookup-instance con)
  (match-define (constraint class type) con)
  (define c-ctx (class-instance-context class))
  (define t-ctx (type-instance-context type))
  (define ent
    (or
     (lookup-instance-entry/context con c-ctx)
     (lookup-instance-entry/context con t-ctx)
     (error 'lookup-instance "should never fail")))
  (if (constraint? (first ent))
      (second ent)
      (error 'lookup-instance
             "TODO: solve \"subgoals\" for instance chaining")))

;; lookup-instance-entry/context : Constraint InstanceContext -> [Maybe InstanceEntry]
(define (lookup-instance-entry/context con ctx)
  (match-define (constraint class type) con)
  (for/or ([ent (in-list ctx)])
    (define ent-con (instance-entry-result-constraint ent))
    (and (constraint-matches? ent-con con)
         ent)))

;; constraint-matches? : Constraint Constraint -> Bool
(define (constraint-matches? con1 con2)
  (match-define (constraint class1 type1) con1)
  (match-define (constraint class2 type2) con2)
  ;; TODO: environment? at link time? or should it be "resolved" by now?
  ;; TODO: should subtyping play a role in this? which direction?
  (and (class=? class1 class2)
       (type=? type1 type2)))


