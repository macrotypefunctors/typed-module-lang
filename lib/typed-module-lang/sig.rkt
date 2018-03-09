#lang agile

;; A Sig is represented with a
;;   (Hashof Symbol SigComponent)

;; A SigComponent is one of:
;;  - (type-alias-decl [TypeWOpaque Symbol])
;;  - (type-opaque-decl)
;;  - (val-decl Type)

(struct type-alias-decl [type] #:prefab)
(struct type-opaque-decl [] #:prefab)
(struct val-decl [type] #:prefab)

;; A [TypeWOpaque X] is one of:
;;  - BaseType
;;  - (-> [TypeWOpaque X] [TypeWOpaque X])
;;  - (opaque-type-reference X)

(struct opaque-type-reference [X] #:prefab)

;; ---------------------------------------------------------

(define (sig-matches? A B)
  ;; process type declarations first
  ;; get the mapping from B's opaque types to A's types
  (define b->a
    (for/fold ([b->a (hash)])
              ([(sym B-comp) (in-hash B)]
               #:when (type-opaque-decl? B-comp))
      #:break (not b->a)
      (let ([A-comp (hash-ref A sym #f)])
        (match A-comp
          [(type-alias-decl t)
           (hash-set b->a sym t)]
          [(type-opaque-decl)
           (hash-set b->a sym (opaque-type-reference sym))]
          [_
           #false]))))
  ;; TODO: A-env and B-env
  (and
   b->a
   (for/and ([(sym B-comp) (in-hash B)])
     (let ([A-comp (hash-ref A sym #f)])
       (and A-comp
            (sig-component-matches? A-comp B-comp b->a))))))

;; TODO: A-env and B-env
(define (sig-component-matches? A B b->a)
  (match* [A B]
    [[(val-decl A) (val-decl B)]
     (type-matches? A B)]
    [[(type-alias-decl A) (type-alias-decl B)]
     (type-equal? A B)]
    [[(type-opaque-decl) (type-opaque-decl)]
     #true]
    [[(type-alias-decl _) (type-opaque-decl)]
     #true]
    [[_ _]
     #false]))

(define (type-equal? A-env B-env A B)
  (and (type-matches? A-env B-env A B)
       (type-matches? B-env A-env B A)))
