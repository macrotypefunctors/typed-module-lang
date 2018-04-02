#lang racket/base

(provide for/list/acc)

;; the body should return 2 values:
;;  - the next value for the acc-id
;;  - the element of the result list
;; the whole form returns 2 values:
;;  - the final value for the acc-id
;;  - the whole result list
;; for/list/acc does not handle #:break in the body
(define-syntax-rule (for/list/acc ([acc-id acc-init])
                                  (clause ...)
                      body ...)
  (for/fold ([acc-id acc-init]
             [rev-list-id '()]
             #:result (values acc-id (reverse rev-list-id)))
            (clause ...)
    (let-values ([(acc-new elem-new)
                  (let () body ...)])
      (values acc-new (cons elem-new rev-list-id)))))

