#lang racket/base

(provide ref def)

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

(define-simple-macro (ref id:id suffix:id ...)
  (elemref (list context-overloading-link (list 'id 'suffix ...))
           (racketkeywordfont (symbol->string 'id))
           (superscript (symbol->string 'suffix)) ...
           #:underline? #f))

(define-simple-macro (def id:id suffix:id ...)
  (elemtag (list context-overloading-link (list 'id 'suffix ...))
           (ref id suffix ...)))

