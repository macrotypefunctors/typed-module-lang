#lang racket/base

(provide (all-defined-out)
         (all-from-out "rep/type.rkt"))

(require racket/match
         (rename-in "rep/type.rkt"
                    [subtype? lsubtype?]
                    [type=? ltype=?])
         "env/combined-env.rkt"
         "env/binding-store.rkt"
         "env/label-env.rkt")

;; Env Id -> TypeDecl or #f
(define (env-lookup-type-decl G X)
  (match-define (env bs le) G)
  (lenv-lookup-type-decl le (binding-store-lookup bs X)))

;; Env Id -> Type or #f
(define (env-lookup-val G x)
  (match-define (env bs le) G)
  (lenv-lookup-val le (binding-store-lookup bs x)))

;; Env Type Type -> Bool
(define (subtype? G τ1 τ2)
  (match-define (env bs le) G)
  (lsubtype? le τ1 τ2))

;; Env Type Type -> Bool
(define (type=? G τ1 τ2)
  (match-define (env bs le) G)
  (ltype=? le τ1 τ2))

