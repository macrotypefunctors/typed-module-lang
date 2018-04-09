#lang racket/base

(provide ref def)

(require (only-in scribble/manual
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

(define-syntax ref
  (syntax-rules ()
    [(ref id suffix ...)
     (elemref (list context-overloading-link (list 'id 'suffix ...))
              (racketkeywordfont (symbol->string 'id))
              (superscript (symbol->string 'suffix)) ...
              #:underline? #f)]))

(define-syntax def
  (syntax-rules ()
    [(def id suffix ...)
     (elemtag (list context-overloading-link (list 'id 'suffix ...))
              (racket id)
              (superscript (symbol->string 'suffix)) ... )]))

