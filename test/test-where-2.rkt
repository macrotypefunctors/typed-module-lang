#lang typed-module-lang

(define-signature S =
  (sig
   (module B : (sig (type t = Bool)))
   (type t)))

(define-module A =
  (mod
    (define-module B =                ;      <--------------- here ---|
      (mod (type X = Int)))           ;                               |
    (define-module C =                ;                               |
      (seal (mod                      ;                               |
             (define-module B =       ;                               |
               (mod (type t = Bool))) ;                               |
             (type t = Int))          ;                               |
            :>                        ;                               |
            (where S t = B.X)))       ; <-- this B *should* refer to >|
    ))

(define-module A* =
  (seal A :> (sig
              (module C : (sig
                           (type t = Int))))))
