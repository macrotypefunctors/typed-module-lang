#lang scribble/manual

@(define git-repo-root "https://github.com/macrotypefunctors/typed-module-lang")
@(define git-repo-branch 'master)
@(define (git-url path)
   (format "~a/tree/~a/~a"
           git-repo-root
           git-repo-branch
           path))
@(define (grammar-spec label)
   (hyperlink (git-url "typed-module-lang/scribblings/grammar.pdf")
              label))

@verbatim|{
To:      Matthias Felleisen, boss
From:    Alex Knauth
         Milo Turner
Subject: Implementing Module / Functor Systems with Macros
}|


@;{-------------------------------------------------------------------}

Our objective is to build an ML-style module and functor system for a
simple typed language. We hope to show how Racket's metaprogramming
facilities can be used to extend an existing typed language with a
module and functor system. To do this, we will build a typed
@deftech{core language}, then extend it with a @deftech{module
language} without modifying the core.


@;{-------------------------------------------------------------------}
@bold{Core Language}

The @tech{core language} will resemble System-F, featuring lambda
functions, application, and polymorphism. The grammar for the core
language is described in the @grammar-spec{grammar specification}, by
the @tt{core-type} and @tt{core-expr} productions.


@;{-------------------------------------------------------------------}
@bold{Module Language}

We will extend


The @tech{Modular Language}. We will build an ML-style module and
functor system for a simple typed language.

A @deftech{module} is either a @tech{mod} or a @tech{functor}.

A @deftech{mod} is what we normally think of as a "concrete" module,
composed of type alias definitions and value definitions. Operations
on @tech{mod}s include selecting a value from the mod and sealing the
mod with a signature.

A @deftech{functor} is a function from @tech{module} to
@tech{module}. Operations on functors include applying a functor to a
@tech{module} to produce another @tech{module} and sealing the functor
with a signature.

A @deftech{signature} as a type for a @tech{module}.

@bold{Motivation}

We want to build this prototype as a proof of concept. We plan to move on to adding modules and functors to Hackett if this is successful.

@bold{Milestones}

@itemlist[
  @item{
    Develop the grammar capabilities of the module language,
    try to think of edge cases early by creating examples.}
  @item{
    Build the simple typed language.}
  @item{
    Create a module system with just @tech{mod}s and @tech{signature}s.}
  @item{
    Implement @tech{functor}s and functor signatures.}
  @item{
    Explore integration of this system into the Hackett language.}
]
