#lang agile

(provide type->string
         sig->string)

(require racket/pretty
         "../type.rkt"
         "../sig.rkt")

(module+ private
  (provide ->s-expr
           ->s-expr/recur))

;; ---------------------------------------------------------

(define (type->string τ)
  (pretty-format (->s-expr τ) #:mode 'write))

(define (sig->string τ)
  (pretty-format (->s-expr τ) #:mode 'write))

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

(define (->s-expr τ)
  (->s-expr/recur τ ->s-expr))

(define (->s-expr/recur τ rec)
  (match τ
    ;; generic things, both types and module paths
    [(named-reference x)
     (cond [(identifier? x) (syntax-e x)]
           [(symbol? x) x]
           [else (unconvertable τ)])]
    [(dot path x)
     (cond [(symbol? x) (*dot (rec path) x)]
           [else (unconvertable τ)])]
    ;; types
    [(Int) 'Int]
    [(Bool) 'Bool]
    [(Arrow ins out)
     `(-> ,@(map rec ins) ,(rec out))]
    ;; signatures
    [(? sig? s)
     `(sig
       ,@(for/list ([(k v) (in-hash s)])
           (match v
             [(val-decl τ)        `(val ,k : ,(rec τ))]
             [(type-opaque-decl)  `(type ,k)]
             [(type-alias-decl τ) `(type ,k = ,(rec τ))]
             [(mod-decl sub)      `(define-module ,k : ,(rec sub))])))]
    [(pi-sig x A B)
     (cond [(identifier? x)
            `(Π ([,(syntax-e x) : ,(rec A)]) ,(rec B))]
           [else
            (unconvertable τ)])]
    ;; else
    [_
     (unconvertable τ)]))

