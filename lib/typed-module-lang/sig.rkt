#lang racket/base
(require racket/match racket/bool)

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
;;  - TODO: ∀

(struct Int [] #:prefab)
(struct opaque-type-reference [X] #:prefab)

;; ---------------------------------------------------------

;; Sig Sig -> Bool
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

  ;; create an identity mapping for A's opaque types
  (define a->a
    (for/hash ([(sym A-comp) (in-hash A)]
               #:when (type-opaque-decl? A-comp))
      (values sym (opaque-type-reference sym))))

  (and b->a
       (for/and ([(sym B-comp) (in-hash B)])
         (let ([A-comp (hash-ref A sym #f)])
           (and A-comp
                (sig-component-matches? a->a b->a
                                        A-comp B-comp))))))

;; [Hash Sym Type] [Hash Sym Type] SigComp SigComp -> Boolean
(define (sig-component-matches? A-env B-env A B)
  (match* [A B]
    [[(val-decl A) (val-decl B)]
     (type-matches? A-env B-env A B)]
    [[(type-alias-decl A) (type-alias-decl B)]
     (type-equal? A-env B-env A B)]
    [[(type-opaque-decl) (type-opaque-decl)]
     #true]
    [[(type-alias-decl _) (type-opaque-decl)]
     #true]
    [[_ _]
     #false]))

;; [Hash Sym Type] [Hash Sym Type] Type Type -> Boolean
(define (type-equal? A-env B-env A B)
  (and (type-matches? A-env B-env A B)
       (type-matches? B-env A-env B A)))

;; [Hash Sym Type] [Hash Sym Type] Type Type -> Boolean
(define (type-matches? A-env B-env A B)
  (match* [A B]
    [[_ _] #:when (equal? A B) #t]

    ;; TODO: function type

    [[(opaque-type-reference x) _]
     #:when A-env
     (type-matches? #f B-env (hash-ref A-env x) B)]

    [[_ (opaque-type-reference y)]
     #:when B-env
     (type-matches? A-env #f A (hash-ref B-env y))]

    [[(opaque-type-reference x) (opaque-type-reference y)]
     (symbol=? x y)]

    [[_ _]
     #false]))


;; -----------------------------------------------------

(module+ test
  (require rackunit racket/function)

  (define empty (hash))
  (define sig-X=int
    (hash
     'X (type-alias-decl (Int))))
  (define sig-X-opaque
    (hash
     'X (type-opaque-decl)))

  (check sig-matches? empty empty)
  (check sig-matches? sig-X=int sig-X=int)
  (check sig-matches? sig-X-opaque sig-X-opaque)

  (check sig-matches? sig-X=int sig-X-opaque)
  (check (negate sig-matches?) sig-X-opaque sig-X=int)


  (define sig-X/Y-x:X
    (hash
     'X (type-opaque-decl)
     'Y (type-alias-decl (opaque-type-reference 'X))
     'x (val-decl (opaque-type-reference 'X))))

  (define sig-X/Y-x:Y
    (hash
     'X (type-opaque-decl)
     'Y (type-opaque-decl)
     'x (val-decl (opaque-type-reference 'Y))))

  (check sig-matches? sig-X/Y-x:X sig-X/Y-x:Y)
  (check (negate sig-matches?) sig-X/Y-x:Y sig-X/Y-x:X)


  (define sig-X-Y=X
    (hash
     'X (type-opaque-decl)
     'Y (type-alias-decl (opaque-type-reference 'X))))

  (define sig-Y-X=Y
    (hash
     'Y (type-opaque-decl)
     'X (type-alias-decl (opaque-type-reference 'Y))))

  (check (negate sig-matches?) sig-X-Y=X sig-Y-X=Y)


  (check sig-matches?
         (hash 'v (val-decl (Int))
               'X (type-alias-decl (Int))
               'Y (type-alias-decl (Int)))
         (hash 'v (val-decl (opaque-type-reference 'X))
               'X (type-opaque-decl)
               'Y (type-alias-decl (opaque-type-reference 'X))))

  (check sig-matches?
         (hash 'X (type-opaque-decl)
               'Y (type-alias-decl (opaque-type-reference 'X)))
         (hash 'Y (type-opaque-decl)))

  )
