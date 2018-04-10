#lang scribble/manual

@(require (for-label typed-module-lang
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
}

@defform[#:literals [=]
         (type id = @#,racket[_rhs-type])]{
Declares a type alias, allowing @racket[_id] to be used interchangeably
with @racket[_rhs-type].
}

@defform[#:literals [=]
         (newtype id = (constructor-id type))]{
Defines a type with a single unary constructor @racket[_constructor-id].
}

@;---------------------------------------------------------------------------------
@subsection{Runtime Expressions}

These forms are for expressions that evaluate to values at runtime.
@overloaded-listing[e #%var λ #%app #%dot]

@defform[(#%datum . n)
         #:contracts ([n exact-integer?])]{
Interposition point for literals. Only integer literals are currently supported.
}

@defform[(let ([id expr] ...) body-expr)]{
Locally binds @racket[_id]s within @racket[_body-expr].
}

@defform[(inst {type ...} expr)]{
Instantiation of quantified types. UNIMPLEMENTED. }

@deftogether[
 [@defthing[+ (-> Int Int Int)]
  @defthing[- (-> Int Int Int)]
  @defthing[* (-> Int Int Int)]]]{
Primitive operations on integers.
}

@;---------------------------------------------------------------------------------
@subsection{Type Expressions}

These forms are for type expressions.
@overloaded-listing[τ #%var #%dot]

@defidform[Int]{The type of exact integers.}

@defform[(-> in-type ... out-type)]{
The type of functions from @racket[in-type]s to @racket[out-type].}

@defform[(∀ (id ...) type)]{
Quantified types. UNIMPLEMENTED. }

@;---------------------------------------------------------------------------------
@section{Module Language}
@subsection{Module Definition Forms}

@defform[#:literals [=]
         (define-module id = mod-expr)]{
Creates a module binding.
}

@defform[#:literals [=]
         (define-signature id = sig-expr)]{
Declares a signature alias, allowing @racket[_id] to be used interchangeably
with @racket[_sig-expr].}

@;---------------------------------------------------------------------------------
@subsection{Module Expressions}

These forms are for module expressions.
@overloaded-listing[m #%var λ #%app]

@defform[(mod def ...)]{
Creates a module structure consisting of the given definitions.}

@defform[#:literals [:>] (seal mod-expr :> sig-expr)]{
Seals the module @racket[_mod-expr] to be constrained by
the signature @racket[_sig-expr]. }

@;---------------------------------------------------------------------------------
@subsection{Signature Expressions}

These forms are for signature expressions.
@overloaded-listing[s #%var]

@defform[#:literals [: =]
         (sig component ...)
         #:grammar
         ([component
           (@#,racket[val] id : @#,racket[_type] = expr)
           (@#,racket[type] id = rhs-type)
           (@#,racket[type] id)])]{
Creates a module signature specifying the given value and type bindings.
A @racket[type] binding with no right-hand side declares the type binding
to be "opaque". }

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
   A functor module. Parameterizes @racket[_mod-expr] over modules
   with signature @racket[_sig-expr]. Can be instantiated with @ref[#%app m].
   Functors may be curried. })

@;---------------------------------------------------------------------------------
@; #%app

@(defidform/overloaded #%app
   #:literals [:]

   @spec[e (#%app func-expr arg-expr ...)]{
   Applies the @racket[_arg-expr]s to the function @racket[_func-expr].}

   @spec[m (#%app functor-expr mod-expr)]{
   Instantiates the functor module @racket[_functor-expr] with @racket[_mod-expr].
   @;TODO: talk about drawbacks when comparing two paths
   })

@;---------------------------------------------------------------------------------
@; #%dot

@(defidform/overloaded #%dot
   @spec[e (#%dot mod-expr id)]{References a value binding in the module @racket[_mod-expr].}
   @spec[τ (#%dot mod-expr id)]{References a type binding in the module @racket[_mod-expr].})
