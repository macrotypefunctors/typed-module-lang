#lang racket/base

(provide label=?
         fresh-label
         empty-label-env
         label-env-lookup
         label-env-extend)

(require racket/bool
         racket/match)

;; An Environment has two parts:
;;  * The BindingStore maps identifiers to unique symbols called "labels"
;;  * The LabelEnv maps the labels to values

;; An [LabelEnvof X] is a [Hashof Label X]
;; (can be called [Lenvof X])

;; Label Label -> Bool
(define (label=? x y)
  (symbol=? x y))

;; Sym -> Label
;; Id -> Label
(define (fresh-label id)
  (cond [(symbol? id) (gensym id)]
        [else         (gensym (syntax-e id))]))

(define (empty-label-env)
  (hash))

;; [LabelEnvof X] Label -> X
(define (label-env-lookup lenv k [els (λ () (error "label not found"))])
  (hash-ref lenv k els))

;; [LabelEnvof X] [Listof [List Label X]] -> [LabelEnvof X]
(define (label-env-extend lenv entries)
  (for/fold ([lenv lenv])
            ([ent (in-list entries)])
    (match-define (list k v) ent)
    (hash-set lenv k v)))

