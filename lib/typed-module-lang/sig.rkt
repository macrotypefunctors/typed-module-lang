#lang racket/base

(provide (all-defined-out)
         (all-from-out "rep/sig.rkt"))

(require racket/match
         (rename-in "rep/sig.rkt"
                    [type-matches? ltype-matches?]
                    [signature-matches? lsignature-matches?])
         "env/combined-env.rkt"
         "env/binding-store.rkt"
         "env/label-env.rkt")

;; Env Id -> Signature or #f
;; return signature of module with given name
(define (env-lookup-module G x)
  (match-define (env bs le _) G)
  (lenv-lookup-module le (binding-store-lookup bs x)))

;; Env Id -> Signature or #f
;; return signature defined by given name
(define (env-lookup-signature G x)
  (match-define (env bs le _) G)
  (lenv-lookup-signature le (binding-store-lookup bs x)))

;; Env ModPath Symbol -> SigEntry or #f
(define (mod-path-lookup G path y)
  (match-define (env bs le _) G)
  (lenv-mod-path-lookup le path y))

;; Env Type Type -> Bool
(define (type-matches? G τ1 τ2)
  (match-define (env bs le _) G)
  (ltype-matches? le τ1 τ2))

;; Env Signature Signature -> Bool
(define (signature-matches? G s1 s2)
  (match-define (env bs le _) G)
  (lsignature-matches? le s1 s2))

;; Env Bindings -> Sig
;; The identifiers in the lhs's of module-bindings are *reference* positions
;; in the env.
(define (module-bindings->sig env module-bindings)
  (for/hash ([p (in-list module-bindings)])
    (match-define (list id binding) p)
    (define label (lookup-label env id))
    (define entry (env-binding->sig-entry binding))
    ;; convert identifiers into symbols for the outside names
    ;; for the signature
    (values (syntax-e id) (sig-component label entry))))

