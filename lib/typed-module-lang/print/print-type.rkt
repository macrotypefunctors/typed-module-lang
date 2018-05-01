#lang agile

(provide type->string
         sig->string)

(require racket/pretty
         syntax/id-table
         "../type.rkt"
         "../sig.rkt")

(module+ private
  (provide ->s-expr
           ->s-expr/recur))

;; ---------------------------------------------------------

(define (type->string τ)
  (define env (make-immutable-free-id-table))
  (pretty-format (->s-expr env τ) #:mode 'write))

(define (sig->string τ)
  (define env (make-immutable-free-id-table))
  (pretty-format (->s-expr env τ) #:mode 'write))

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

;; An Env is a [FreeIdTableOf Symbol]
;; maps identifiers to their *external*-ly seen names

(define (->s-expr env τ)
  (->s-expr/recur env τ ->s-expr))

(define (->s-expr/recur env τ rec)
  (define (rc τ) (rec env τ))
  (match τ
    ;; generic things, both types and module paths
    [(named-reference (? identifier? x))
     (free-id-table-ref env x (λ () (syntax-e x)))]
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
       (for/fold ([env* env]) ([(k v) (in-hash s)])
         (match-define (sig-component id _) v)
         (free-id-table-set env* id k)))
     `(sig
       ,@(for/list ([(k v) (in-hash s)])
           (match-define (sig-component _ entry) v)
           (match entry
             [(val-decl τ)        `(val ,k : ,(rec env* τ))]
             [(type-opaque-decl)  `(type ,k)]
             [(type-alias-decl τ) `(type ,k = ,(rec env* τ))]
             [(mod-decl sub)      `(module ,k : ,(rec env* sub))])))]
    [(pi-sig (? identifier? x) A B)
     (define env*
       (free-id-table-set env x (syntax-e x)))
     `(Π ([,(syntax-e x) : ,(rc A)]) ,(rec env* B))]
    ;; else
    [_
     (unconvertable τ)]))
