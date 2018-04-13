#lang scribble/manual

@(require (for-label (except-in typed-module-lang =)
                     (except-in racket/contract/base ->))
          (for-syntax racket/base syntax/parse)
          racket/list
          racket/match
          racket/contract/base
          "context-overloading.rkt")

@;--------------------------------------------------------------
@;--------------------------------------------------------------
@;--------------------------------------------------------------

@title{Typed Module Lang}

@defmodule[typed-module-lang #:lang]

@; TODO: paragraph introducing the language
@; TODO: explain the new interposition pts (#%dot, #%var)

@;---------------------------------------------------------------------------------
@section{Core Language}
@subsection{Definition Forms}

@defform[#:literals [: =]
         (val id : type = expr)]{
Creates a value binding.

@racketblock[(val hyol : Int = 4620)]
}

@defform[#:literals [=]
         (type id = @#,racket[_rhs-type])]{
Declares a type alias, allowing @racket[_id] to be used interchangeably
with @racket[_rhs-type].

@racketblock[(type CRN = Int)]
}

@defform[#:literals [=]
         (check actual-expr = expected-expr)]{
Performs a test that the two expressions yield the same value. Internally
uses rackunit's @racket[check-equal?].

@racketblock[(check (fib 16) = 987)]
}

@;---------------------------------------------------------------------------------
@subsection{Runtime Expressions}

These forms are for expressions that evaluate to values at runtime.
@overloaded-listing[e #%var λ #%app #%dot]

@defform[(#%datum . n)
         #:contracts ([n (or/c exact-integer? boolean?)])]{
Interposition point for literals. Supports exact integers and booleans.
}

@defform[(let ([id expr] ...) body-expr)]{
Locally binds @racket[_id]s within @racket[_body-expr].

@racketblock[(let ([x 9]) (+ x 1))]
}

@defform[(if question-expr then-expr else-expr)]{
Evaluates @racket[_then-expr] if @racket[_question-expr] evaluates
to @racket[#t], otherwise evaluates @racket[_else-expr].

@racketblock[
(val not : (-> Bool Bool)
  (λ (x) (if x #f #t)))]
}

@defform[(inst {type ...} expr)]{Instantiates a polymorphic expression. UNIMPLEMENTED. }
@defform[(Λ (type ...) expr)]{Universally quantifies an expression. UNIMPLEMENTED. }

@deftogether[
 [@defthing[+ (-> Int Int Int)]
  @defthing[- (-> Int Int Int)]
  @defthing[* (-> Int Int Int)]
  @defthing[quo (-> Int Int Int)]
  @defthing[rem (-> Int Int Int)]
  @defthing[< (-> Int Int Bool)]
  @defthing[> (-> Int Int Bool)]
  @defthing[= (-> Int Int Bool)]]]{
Primitive operations on integers.
}

@;---------------------------------------------------------------------------------
@subsection{Type Expressions}

These forms are for type expressions.
@overloaded-listing[τ #%var #%dot]

@defidform[Int]{The type of exact integers.}
@defidform[Bool]{The type of booleans (@racket[#t] or @racket[#f]).}

@defform[(-> in-type ... out-type)]{
The type of functions from @racket[in-type]s to @racket[out-type].}

@defform[(∀ (id ...) type)]{
Quantified types. UNIMPLEMENTED. }

@;---------------------------------------------------------------------------------
@section{Module Language}
@subsection{Module Definition Forms}

@defform[#:literals [=]
         (define-module id = mod-expr)]{
Creates a module binding. The @racket[_mod-expr] is immediately
instantiated if it is not a functor.

@racketblock[
(define-module M =
  (mod (val x : Int = 4)))]
}

@defform[#:literals [=]
         (define-signature id = sig-expr)]{
Declares a signature alias, allowing @racket[_id] to be used interchangeably
with @racket[_sig-expr].

@racketblock[
(define-signature S =
  (sig (val x : Int)))]
}

@;---------------------------------------------------------------------------------
@subsection{Module Expressions}

These forms are for module expressions.
@overloaded-listing[m #%var λ #%app #%dot]

@defform[(mod def ...)]{
Creates a module structure consisting of the given definitions.

@racketblock[
(define-module Image =
  (mod (type Color = Int)
       (type Image = (-> Int Int Color))
       (val black : Color = 0)
       (val white : Color = 100)
       (val blank : Image = (λ (x y) white))))]

Module structures are allowed to contain @racket[check]s, which are
run when the module is instantiated.

@racketblock[
(define-module Tests =
  (mod
    (check (Image.blank 0 0) = Image.white)))]

Module structures may contain submodules, using nested @racket[define-module]s:

@racketblock[
(define-module Painting =
  (mod
    (define-module Brush =
      (mod (type T = (-> Bool Int))
           (val size : (-> T Int) (λ (br) (br #t)))
           (val color : (-> T Image.Color) (λ (br) (br #f)))))
    (val default-brush : Brush.T =
      (λ (i) (if i 1 Color.black)))))]

Submodules are experimental and sometimes act in unexpected ways. For instance,
all submodule definitions are moved to the front of a module, and may only
access submodules above them. }

@defform[#:literals [:>] (seal mod-expr :> sig-expr)]{
Seals the module @racket[_mod-expr] to be constrained by
the signature @racket[_sig-expr].

@racketblock[
(define-signature COUNT
  (type T)
  (val dec : (-> T T))
  (val inc : (-> T T)))

(define-module Count
  (seal (mod (type T = Int)
             (val inc : (-> T T) (λ (x) (+ x 1)))
             (val dec : (-> T T) (λ (x) (- x 1))))
        :> COUNT))

(val n : Int = (Count.inc 0)) (code:comment @#,elem{Does not typecheck, since T is opaque})]}

@;---------------------------------------------------------------------------------
@subsection{Signature Expressions}

These forms are for signature expressions.
@overloaded-listing[s #%var]

@defform[#:literals [: =]
         (sig component ...)
         #:grammar
         ([component
           (@#,racket[val] id : @#,racket[_type])
           (@#,racket[type] id = rhs-type)
           (@#,racket[type] id)])]{
Creates a module signature specifying the given value and type bindings.
A @racket[type] binding with no right-hand side declares the type binding
to be ``opaque''. }

@defform[#:literals [:]
         (Π ([id : in-sig-expr]) out-sig-expr)]{
Creates a module signature specifying functors with the given
input and output signatures. @racket[_id] is bound within @racket[_out-sig-expr]. }

@;=================================================================================
@section{Context-Dependent Forms}

@;---------------------------------------------------------------------------------
@; #%var

@(defidform/overloaded #%var
   @spec[e (#%var id)]{A reference to a variable in an expression.}
   @spec[τ (#%var id)]{A reference to a type.}
   @spec[m (#%var id)]{A reference to a module.}
   @spec[s (#%var id)]{A reference to a signature.})

@;---------------------------------------------------------------------------------
@; λ

@(defidform/overloaded λ
   #:literals [:]

   @spec[e (λ ([id : type] ...) expr)]{
   Produces a lambda function.}

   @spec[e (λ (id ...) expr)]{
   Variant of @ref[λ e] without annotations. Must only be used in
   a context where the types can be easily inferred (e.g. in the
   body of a @racket[val] definition).}

   @spec[m (λ ([id : sig-expr]) mod-expr)]{
   Produces a functor module which parameterizes @racket[_mod-expr] over modules
   with signature @racket[_sig-expr]. Can be instantiated with @ref[#%app m].
   Functors may be curried. })

@;---------------------------------------------------------------------------------
@; #%app

@(defidform/overloaded #%app
   #:literals [:]

   @spec[e (#%app func-expr arg-expr ...)]{
   Applies the @racket[_arg-expr]s to the function @racket[_func-expr].}

   @spec[m (#%app functor-expr mod-path)]{
   Instantiates the functor module @racket[_functor-expr] with @racket[_mod-path].
   Note that the argument must be a path (a series of @ref[#%dot m] or @ref[#%var m]s);
   arbitrary module expressions are not supported.
   })

@;---------------------------------------------------------------------------------
@; #%dot

@(defidform/overloaded #%dot
   @spec[e (#%dot mod-expr id)]{References a value binding in the module @racket[_mod-expr].}
   @spec[τ (#%dot mod-expr id)]{References a type binding in the module @racket[_mod-expr].}
   @spec[m (#%dot mod-path id)]{References a submodule in the module @racket[_mod-expr].})
