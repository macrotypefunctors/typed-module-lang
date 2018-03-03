#lang s-exp syntax/module-reader
typed-module-lang/lang
#:wrapper1 wrapper1

(define (wrapper1 thunk)
  ;; setting `read-cdot` introduces a new
  ;; interposition point macro that must be
  ;; provided by the language: `#%dot`
  (parameterize ([read-cdot #true])
    (thunk)))
