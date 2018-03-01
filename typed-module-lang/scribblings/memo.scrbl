#lang scribble/manual

@(define git-repo-root "https://github.com/macrotypefunctors/typed-module-lang")
@(define git-repo-branch 'master)
@(define (git-url path)
   (format "~a/tree/~a/~a"
           git-repo-root
           git-repo-branch
           path))
@(define (grammar-spec [label "grammar specification"])
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
@tech{core language}, then extend it with a @tech{module
language} without modifying the core.


@;{-------------------------------------------------------------------}
@bold{Core Language}

The @deftech{core language} will be the second-order lambda calculus,
which features lambda functions, application, and polymorphism. The
grammar for the core language is described in the @grammar-spec[].


@;{-------------------------------------------------------------------}
@bold{Module Language}

Like ML, the @deftech{module language} will come with its own semantics
and typing rules. "Values" in the module language are called
@tech{modules}, and the "types" of these modules are called
@tech{signatures}. The grammar for modules and signatures are
described in the @grammar-spec[].

A @deftech{module} can be either a @tech{mod} or a @tech{functor}.  A
@deftech{mod} (sometimes referred to as a @emph{structure}) is a
collection of type and value definitions. A @deftech{functor} is a
@tech{module} that is parameterized over another module, and can be
conceptualized as a "function" from modules to modules.

Operations on modules include applying a functor to a @tech{module} to
produce another @tech{module}, and sealing the module with a
@tech{signature}. Our module language will not support features such
as nested modules or recursive functors.

A @deftech{signature} as a type for a @tech{module}.

We want to build this prototype as a proof of concept. We plan to move
on to adding modules and functors to Hackett if this is successful.

@;{-------------------------------------------------------------------}
@bold{Milestones}

@itemlist[
  @item{Develop the grammar capabilities of the module language;
        anticipate edge cases by building significant examples.}
  @item{Build the typed core language.}
  @item{Create the first iteration of the module system, featuring only
        @tech{mod} and @tech{sig}

  Create a module system with just @tech{mod}s and @tech{signature}s.}
  @item{
    Implement @tech{functor}s and functor signatures.}
  @item{
    Explore integration of this system into the Hackett language.}
]}
