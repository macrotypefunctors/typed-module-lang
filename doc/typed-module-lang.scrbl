#lang scribble/manual

@(require (for-label typed-module-lang)
          "context-overloading.rkt")

@title{Typed Module Lang}

@defmodule[typed-module-lang #:lang]

@defidform[#%var]{
One of @ref[#%var e], @ref[#%var τ], @ref[#%var m], or @ref[#%var s],
depending on the context.
}

@specsubform[(@#,def[#%var e] id)]{
A reference to a variable in an expression.
}

@specsubform[(@#,def[#%var τ] id)]{
A reference to a type.
}

@specsubform[(@#,def[#%var m] id)]{
A reference to a module.
}

@specsubform[(@#,def[#%var s] id)]{
A reference to a signature.
}

