#lang racket/base

(provide type->string
         constraint->string
         sig->string)

(require racket/match
         racket/pretty
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
  (define le (env-label-env env))
  (pretty-format (->s-expr ne le τ) #:mode 'write))

(define (constraint->string env τ)
  (define ne (env-name-env env))
  (define le (env-label-env env))
  (pretty-format (->s-expr ne le τ) #:mode 'write))

(define (sig->string env τ)
  (define ne (env-name-env env))
  (define le (env-label-env env))
  (pretty-format (->s-expr ne le τ) #:mode 'write))

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

(define (->s-expr ne le τ)
  (->s-expr/recur ne le τ ->s-expr))

(define (->s-expr/recur ne le τ rec)
  (define (rc τ) (rec ne le τ))
  (match τ
    ;; generic things, both types and module paths
    [(label-reference label)
     (label-env-lookup ne label (λ () label))]
    [(dot path (? symbol? x))
     (*dot (rc path) x)]
    ;; types
    [(Int) 'Int]
    [(Bool) 'Bool]
    [(Arrow ins out)
     `(-> ,@(map rc ins) ,(rc out))]
    [(Forall Xs body)
     (define ne* (label-env-extend ne (map list Xs Xs)))
     (define le* (label-env-extend le (for/list ([X (in-list Xs)])
                                        (list X (type-binding
                                                 (type-opaque-decl))))))
     `(∀ ,Xs ,(rec ne* le* body))]
    [(Qual con body)
     `(=> ,(rc con) ,(rc body))]
    [(constraint class type)
     `(,(rc class) ,(rc type))]
    ;; signatures
    [(? sig? s)
     (define ne*
       (label-env-extend ne
                         (for/list ([(k v) (in-hash s)])
                           (match-define (sig-component label _) v)
                           (list label k))))
     (define le*
       (label-env-extend le
                         (for/list ([(k v) (in-hash s)])
                           (match-define (sig-component label ent) v)
                           (list label (sig-entry->env-binding ent)))))
     `(sig
       ,@(for/list ([(k v) (in-hash s)])
           (match-define (sig-component _ entry) v)
           (match entry
             [(constructor-decl τ) `(constructor ,k : ,(rec ne* le* τ))]
             [(data-decl ls)
              (define variants
                (for/list ([l (in-list ls)])
                  (define name (label-env-lookup ne* l))
                  (match (label-env-lookup le* l)
                    [(constructor-binding (Arrow ins (label-reference _)))
                     (cons name (for/list ([in (in-list ins)])
                                  (rec ne* le* in)))])))
              `(data ,k = ,@variants)]
             [(val-decl τ)         `(val ,k : ,(rec ne* le* τ))]
             [(type-opaque-decl)   `(type ,k)]
             [(type-alias-decl τ)  `(type ,k = ,(rec ne* le* τ))]
             [(mod-decl sub)       `(module ,k : ,(rec ne* le* sub))])))]
    [(pi-sig x A B)
     (define ne*
       (label-env-extend ne (list (list x x))))
     (define le*
       (label-env-extend le (list (list x (mod-binding A)))))
     `(Π ([,x : ,(rc A)]) ,(rec ne* le* B))]
    ;; else
    [_
     (unconvertable τ)]))
