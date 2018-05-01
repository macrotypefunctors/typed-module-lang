#lang racket/base

(provide for/free-id-table)

(require syntax/id-table
         syntax/parse/define)

(define-simple-macro (for/free-id-table (clause ...)
                       body:expr ...+)
  (for/fold ([acc (make-immutable-free-id-table)])
            (clause ...)
    (let-values ([(k v) (let () body ...)])
      (free-id-table-set acc k v))))
