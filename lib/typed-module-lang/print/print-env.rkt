#lang racket/base

(provide print-bindings)

(require racket/list
         racket/match
         racket/pretty
         racket/string
         "../type.rkt"
         "../sig.rkt"
         "../env/combined-env.rkt"
         "../env/label-env.rkt"
         "print-type.rkt"
         (submod "print-type.rkt" private))

(define (print-bindings env bindings [out (current-output-port)])
  (for ([entry (in-list (reverse bindings))])
    (pretty-write
     (convert env entry)
     out)))

(struct fmt [str vs] #:transparent
  #:methods gen:custom-write
  [(define (write-proc self out mode)
     (match-define (fmt str vs) self)
     (apply fprintf out str vs))])

(define (convert env entry)
  (define ne (env-name-env env))
  (define le (env-label-env env))
  (match-define (list x-id binding) entry)
  (define x (syntax-e x-id))
  (match binding
    ;; constructor-binding must be matched before val-binding
    [(constructor-binding τ) (fmt "constructor ~s : ~s" (list x (->s-expr ne le τ)))]
    [(val-binding τ) (fmt "val ~s : ~s" (list x (->s-expr ne le τ)))]
    [(type-binding type-decl)
     (match type-decl
       [(type-opaque-decl)  (fmt "type ~s" (list x))]
       [(type-alias-decl τ) (fmt "type ~s = ~s" (list x (->s-expr ne le τ)))]
       [(data-decl labels)
        (define variants
          (for/list ([l (in-list labels)])
            (define constr-name (label-env-lookup ne l))
            (match (label-env-lookup le l)
              [(constructor-binding (Arrow ins (label-reference _)))
               (cons constr-name (for/list ([in (in-list ins)])
                                   (->s-expr ne le in)))])))
        (fmt (string-join #:before-first "data ~s =\n  "
                          (make-list (length variants) "~s")
                          "\n  ")
             (cons x variants))])]
    [(mod-binding s) (fmt "module ~s : ~s" (list x (->s-expr ne le s)))]
    [(sig-binding s) (fmt "signature ~s = ~s" (list x (->s-expr ne le s)))]))

