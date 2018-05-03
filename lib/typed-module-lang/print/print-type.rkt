#lang agile

(provide type->string
         sig->string)

(require racket/pretty
         "../type.rkt"
         "../sig.rkt"
         "../env/combined-env.rkt"
         "../env/label-env.rkt")

(module+ private
  (provide ->s-expr
           ->s-expr/recur))

;; ---------------------------------------------------------

(define (type->string env τ)
  (define ne (env-name-env env))
  (pretty-format (->s-expr ne τ) #:mode 'write))

(define (sig->string env τ)
  (define ne (env-name-env env))
  (pretty-format (->s-expr ne τ) #:mode 'write))

;; ---------------------------------------------------------

(struct unconvertable [v] #:transparent
  #:methods gen:custom-write
  [(define (write-proc self out mode)
     (write (unconvertable-v self) out))])

(struct *dot [m x] #:transparent
  #:methods gen:custom-write
  [(define (write-proc self out mode)
     (match-define (*dot m x) self)
     (fprintf out "~s.~s" m x))])

;; ---------------------------------------------------------

;; A NameEnv is a [LabelEnvof Symbol]
;; maps identifiers to their *external*-ly seen names

(define (->s-expr env τ)
  (->s-expr/recur env τ ->s-expr))

(define (->s-expr/recur env τ rec)
  (define (rc τ) (rec env τ))
  (match τ
    ;; generic things, both types and module paths
    [(label-reference label)
     (label-env-lookup env label (λ () label))]
    [(dot path (? symbol? x))
     (*dot (rc path) x)]
    ;; types
    [(Int) 'Int]
    [(Bool) 'Bool]
    [(Arrow ins out)
     `(-> ,@(map rc ins) ,(rc out))]
    ;; signatures
    [(? sig? s)
     (define env*
       (label-env-extend env
                         (for/list ([(k v) (in-hash s)])
                           (match-define (sig-component label _) v)
                           (list label k))))
     `(sig
       ,@(for/list ([(k v) (in-hash s)])
           (match-define (sig-component _ entry) v)
           (match entry
             [(val-decl τ)        `(val ,k : ,(rec env* τ))]
             [(type-opaque-decl)  `(type ,k)]
             [(type-alias-decl τ) `(type ,k = ,(rec env* τ))]
             [(mod-decl sub)      `(module ,k : ,(rec env* sub))])))]
    [(pi-sig x A B)
     (define env*
       (label-env-extend env (list (list x x))))
     `(Π ([,x : ,(rc A)]) ,(rec env* B))]
    ;; else
    [_
     (unconvertable τ)]))
