#lang scribble/manual

@(require (for-label typed-module-lang)
          (for-syntax racket/base syntax/parse)
          racket/list
          "context-overloading.rkt")

@title{Typed Module Lang}

@defmodule[typed-module-lang #:lang]

@; TODO: paragraph introducing the language

@; TODO: explain the new interposition pts (#%dot, #%var)
@; TODO: explain the superscript forms

@(define (one-of/overloaded main-id . sufs)
   `("One of "
     ,@(append*
        (for/list ([suf (in-list sufs)])
          (define comma
            (cond [(eq? suf (first sufs)) ""]
                  [(eq? suf (last sufs)) ", or "]
                  [else ", "]))
          (list comma (ref* main-id suf))))
     ", depending on the context."))

@(define-syntax defidform/overloaded
   (syntax-parser
     #:datum-literals [spec]
     [(_ main-id:id
         (spec suf:id form body ...)
         ...)
      #:with [form* ...] (map (λ (suf* form)
                                (syntax-parse form
                                  [(id . rst)
                                   #:with suf suf*
                                   #:with id/def (syntax/loc #'id @#,def[id suf])
                                   (syntax/loc form (id/def . rst))]))
                              (attribute suf)
                              (attribute form))
      #'(begin
          (defidform main-id (one-of/overloaded 'main-id 'suf ...))
          (specsubform form* body ...)
          ...)]))

@; --------------------------------------------------
@; #%var

@(defidform/overloaded #%var
   @spec[e (#%var id)]{A reference to a variable in an expression.}
   @spec[τ (#%var id)]{A reference to a type.}
   @spec[m (#%var id)]{A reference to a module.}
   @spec[s (#%var id)]{A reference to a signature.})
