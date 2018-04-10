#lang racket/base

(provide (all-defined-out))

(require syntax/parse/define
         racket/match
         racket/list
         (for-syntax racket/base syntax/parse)
         (only-in scribble/manual
                  defidform
                  specsubform
                  elemref
                  elemtag
                  racket
                  racketkeywordfont
                  italic
                  superscript))

(define context-overloading-link 'context-overloading-link)

(define (ref* id . sufs)
  (elemref (list context-overloading-link (cons id sufs))
           (racketkeywordfont (symbol->string id))
           (map (λ (s) (superscript (symbol->string s))) sufs)
           #:underline? #f))

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
  (ref* 'id 'suffix ...))

(define-simple-macro (def id:id suffix:id ...)
  (elemtag (list context-overloading-link (list 'id 'suffix ...))
           (ref id suffix ...)))

(define (one-of/overloaded main-id . sufs)
  (match (remove-duplicates sufs)
    [(list fst mid ... fin)
     `("One of "
       ,(ref* main-id fst)
       ,(map (λ (suf) (list ", " (ref* main-id suf))) mid)
       ", or "
       ,(ref* main-id fin)
       ", depending on the context.")]
    [(list suf) ""]))

(define-syntax defidform/overloaded
  (syntax-parser
    #:datum-literals [spec]
    [(_ main-id:id
        {~and options {~not (spec . _)}} ...
        (spec suf:id form body ...)
        ...)
     #:with [form* ...]
     (for/fold ([forms '()] [seen '()] #:result (reverse forms))
               ([suf-stx (in-list (attribute suf))]
                [form (in-list (attribute form))])
       (syntax-parse form
         [(id . rst)
          #:with suf suf-stx
          #:with def* (if (memq (syntax-e suf-stx) seen) #'ref #'def)
          #:with id/def (syntax/loc #'id #,(def* id suf))
          (define form* (syntax/loc form (id/def . rst)))
          (values (cons form* forms)
                  (cons (syntax-e suf-stx) seen))]))
     #'(begin
         (defidform main-id (one-of/overloaded 'main-id 'suf ...))
         (specsubform options ... form* body ...)
         ...)]))

(define-syntax-rule (overloaded-listing suffix form ... last-form)
  (list "Some of these forms are overloaded by other phases, "
        "so they are distinguished with a superscript "
        (italic "`" (symbol->string 'suffix) "'") ": "
        (list (ref form suffix) ", ") ...
        (ref last-form suffix) ". "))
