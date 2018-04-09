#lang racket/base

(provide ref* ref def)

(require syntax/parse/define
         (only-in scribble/manual
                  elemref
                  elemtag
                  racket
                  superscript
                  racketkeywordfont))

(define context-overloading-link 'context-overloading-link)

;; examples:
;;   @#,ref[lambda e]
;;   @#,ref[lambda m]
;;   @#,ref[#%var e]
;;   @#,ref[#%var τ]
;;   @#,ref[#%var m]
;;   @#,ref[#%var s]
;;   @#,ref[#%dot e]
;;   @#,ref[#%dot τ]

(define (ref* id . sufs)
  (elemref (list context-overloading-link (cons id sufs))
           (racketkeywordfont (symbol->string id))
           (map (λ (s) (superscript (symbol->string s))) sufs)
           #:underline? #f))

(define-simple-macro (ref id:id suffix:id ...)
  (ref* 'id 'suffix ...))

(define-simple-macro (def id:id suffix:id ...)
  (elemtag (list context-overloading-link (list 'id 'suffix ...))
           (ref id suffix ...)))
