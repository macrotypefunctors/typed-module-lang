#lang agile

(provide print-env)

(require racket/pretty
         "../type.rkt"
         "../sig.rkt"
         "print-type.rkt"
         "../util/for-id-table.rkt"
         (submod "print-type.rkt" private))

(define (print-env G [out (current-output-port)])
  (define rename-env
    (for/free-id-table ([entry (in-list G)])
      (values (first entry) (syntax-e (first entry)))))
  (for ([entry (in-list G)])
    (pretty-write
     (convert rename-env entry)
     out)))

(struct fmt [str vs] #:transparent
  #:methods gen:custom-write
  [(define (write-proc self out mode)
     (match-define (fmt str vs) self)
     (apply fprintf out str vs))])

(define (convert rnm-env entry)
  (match-define (list x-id binding) entry)
  (define x (syntax-e x-id))
  (match binding
    [(val-binding τ) (fmt "val ~s : ~s" (list x (->s-expr rnm-env τ)))]
    [(type-binding type-decl)
     (match type-decl
       [(type-opaque-decl)  (fmt "type ~s" (list x))]
       [(type-alias-decl τ) (fmt "type ~s = ~s" (list x (->s-expr rnm-env τ)))])]
    [(mod-binding s) (fmt "module ~s : ~s" (list x (->s-expr rnm-env s)))]
    [(sig-binding s) (fmt "signature ~s = ~s" (list x (->s-expr rnm-env s)))]))

