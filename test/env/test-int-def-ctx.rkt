#lang racket
(module rackunit+ racket
  (require rackunit)
  (provide (all-from-out rackunit) check-free-id=? check-bound-id=?)
  (define-binary-check (check-free-id=? free-identifier=? id-lhs id-rhs))
  (define-binary-check (check-bound-id=? bound-identifier=? id-lhs id-rhs)))

(module+ test
  (require (for-syntax racket
                       (submod ".." rackunit+)
                       typed-module-lang/env/int-def-ctx))

  (begin-for-syntax
    (match-define (list X Y Z)
      (generate-temporaries #'[x y z]))

    (define E0 (empty-env))

    (define E1 (extend E0 `([,X "a"] [,Y "b"])))
    (check-equal? (lookup E1 X) "a")
    (check-equal? (lookup E1 Y) "b")

    (define E1.5 (extend E0 `([,X "a"])))
    (check-exn exn:fail? (λ () (lookup E1.5 Y)))

    (define E2 (extend E1 `([,Z "c"])))
    (check-equal? (lookup E2 X) "a")
    (check-equal? (lookup E2 Y) "b")
    (check-equal? (lookup E2 Z) "c")

    (match-define `([,Z* "c"] [,X* "a"] [,Y* "b"])
      (env->assoc E2))

    (check-bound-id=? X X*)
    (check-bound-id=? Y Y*)
    (check-bound-id=? Z Z*)
    ))
