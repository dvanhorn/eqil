#lang scribble/lncs
@(require (only-in scribble/manual racketmod)
          slideshow/pict
          redex/pict
          "semantics.rkt"
          scriblib/figure)

@(define-syntax-rule
   (qil e)
   (render-term EQIL e))

@title{Abstracting Coq}
@authors[@author{David Van Horn}]
@institutes[@institute{PRL, Northeastern University}]
         
@abstract{These notes step through the design and implementation 
          of an abstract interpreter for an intermediate language
          for Coq, i.e. a Curry-style typed lambda-calculi in 
          continuation-passing style that is pure and total.}

Greg told me that you're building a compiler for Coq and one of
the things you'd like this compiler to do is perform @emph{abstract
interpretation} (or @emph{program analysis}) to inform optimizations,
program transformations, and other things compilers are in the
business of doing.  I had new stuff I wanted to come over and talk
about, so he said why don't you just come over and lecture on this
stuff.  That was Friday.  Today it's Wednesday and below you find
a fairly complete solution to the problem.  That's not bad turn-around,
particulary considering that time includes a coast-to-coast flight
and the largest Atlantic hurricane in diameter on record.

@section{A note on approach}

A lesson I learned a long time ago was 

@centered{@emph{an abstract interpreter is just a kind of interpreter.}}

But that's probably not the first thing
that pops out at you when you see the co-inductive ``acceptability'' 
judgments for 0-CFA in @emph{Principles of Program Analysis}.  
And it's probably the last
thing that pops out at you when you see the table of source/sink flow
relations in Meunier, Findler, Felleisen (POPL, 1996).  So if abstract
interpreters are just interpreters, why do they look so different?
My perspective is these differences can be a serious impediment to
the rapid prototyping of analyzers for sophisticated languages: they 
require extensive design and verification effort to show they
soundly approximate the semantics of the language.
But these differences can be eliminated.
In these notes, I'll show how to make program analyzers
that look a lot more like program interpreters.
(For further details, see 
@emph{Systematic Abstraction of Abstract Machines}, JFP, 2012.)

The basic idea of the approach is to write down the semantics
of your language as an abstract machine.  If you can write down the
semantics in just about any widely-used style (e.g. definitional interpreter, 
structural operational semantics, denotational semantics, 
reduction semantics, etc.) you can
systematically transform that semantics into an abstract machine, 
so starting from abstract machines offers a good general 
purpose starting point.  It's important that this machine
heap-allocate all potentially infinitary structure (i.e. all 
recursive structure).  For a functional language in direct-style,
that means variable bindings and continuations must be heap-allocated.
In a CPS language like we're considering here, it means
variable bindings (all continuations are trivial).

Starting from a machine in this form, the simplest way to make a sound
computable approximation is to
@itemlist[
  @item{change the heap to map locations to @emph{sets} of storable values,}
  @item{restrict allocation to a finite set of locations,}
  @item{replace heap updates with joins, and }
  @item{replace heap dereferences with non-deterministic choice.}
  ]

This will give a finite approximation to the @emph{control} and @emph{environment}
structure of a program.  You'll also have to give a finite approximation
of base @emph{data} if your language includes infinite-sized base domains
like the natural numbers.

@section{A note on tools}

I use Redex, a domain-specific language for semantics engineering.
I use Redex all the time and think it's a great tool.  You should
think of Redex as the scripting language of mechanized metatheory.
There are multiple papers I've written that I could have written
without Redex because I simply would not have been able to complete
the research.  Redex makes it easy to run, test, typeset, and experiment
with semantic models.

We'll use it to define the interpreter and its abstract counterpart.
From the semantic modes, it's easy to actually make these programming
languages supported by the DrRacket development environment, which is
useful to interactions and testing.  Redex and DrRacket are part of
the Racket programming language, available at:

@centered{@url{http://racket-lang.org/}}

You can read more about Redex and find links to the book, 
@emph{Semantics Engineering with PLT Redex}, by Felleisen, Findler, and Flatt,
at:

@centered{@url{http://redex.racket-lang.org/}}
          
For a compelling case in favor of using Redex, see Robby Findler's POPL
2012 talk on @emph{Run Your Research}:

@centered{@url{http://www.youtube.com/watch?v=BuCRToctmw0}}

@section{A note on code}

All the source is available from:

@centered{@url{https://github.com/dvanhorn/eqil}}

@section{Outline}

In @secref{syntax}, I piece together the notes Greg sent me
on the syntax of the Coq IL and turn them into a language
definition in Redex, which I name QIL.

In @secref{semantics}, I then give a reduction semantics for
Coq IL that characterizes the run-time behavior of a program
as traces of machine transitions for a Coq IL interpreter.
The interpreter uses an environment and store (or heap).

In @secref{abstract-semantics}, I refactor the semantics
to be easily and soundly abstractable by varying the
heap allocation strategy.  Finite heap allocation strategies
give rise to computable abstract interpretations of Coq IL programs.

@section[#:tag "syntax"]{Syntax of Coq IL}

@subsection{Notes from Greg}

Our CPS language looks like this:

@verbatim[#:indent 4]{
                      
v ::= x | c

e ::= v(v1,...,vn)
   | let x = d in e
   | switch v in {c1 => e1 | ... | cn => en}
   | halt v

d ::= x = prim(v1,...,vn)
      x = <v1,...,vn>
      x = #i v
      x = \x.e
      rec d1 ... dn
      
}

The intuition is that @tt{v} classifies ``small'' values that don't need
to be allocated (variables, constants -- and hence can be freely
substituted) and ``large'' values such as lambdas (closures) and tuples 
are allocated.

I've abused notation and overloaded variable declarations as
program points, because we are maintaining a convention that
each variable has a unique name throughout the code.  

Technically it's limited to recursive declarations of
functions and tuples.  Pre-closure conversion, it's limited
to functions.  So it's (bad) notation for what should really
be:

@verbatim[#:indent 4]{
          
   rec x1 = \x1.e1
       ...
       xn = \xn.en

}

Post-closure conversion, we use recursive tuples to build 
the circular environments, hence we have both:

@verbatim[#:indent 4]{
     
   rec x1 = \x1.e1
       ...
       xn = \xn.en

}
and
@verbatim[#:indent 4]{
          
   rec x1 = <v11,...,v1n1>
       ...
       xm = <vm1,....,vmnm>

}

@subsection{QIL in Redex}

Here is the
(slightly touched-up) translation of the grammar
into a language definition in Redex.
I assumed constants include natural numbers, threw in
a few numeric primitives, and sprinkled liberally with parentheses.

@(centered (render-language QIL))

As an example of a program written in this language, here
is the factorial of 5:

@#reader scribble/comment-reader
(racketmod
  eqil
  (rec (fact = (λ n k
                 (let r = (= n 0)
                   in
                   (switch r in
                     (0 => (k 1))
                     (1 => (let n-1 = (sub1 n) in
                             (let m = (λ n-1!
                                        (let t = (* n n-1!) in
                                          (k t)))
                               in
                               (fact n-1 m))))))))
    in
    (let id = (λ x (halt x)) in
      (fact 5 id)))
    )
  
@section[#:tag "semantics"]{An interpreter for Coq IL}

Here is the transition relation for QIL.  There are four cases: 
function application, let reduction, recursive definitions, and
switching.

@(figure-here "step" "Reduction relation for EQIL" 
              (render-reduction-relation step #:style 'vertical))

A function application @(qil ((X_f V ...) ρ σ))
reduces by dereferencing the operation @(qil X_f) to get a function
@(qil ((λ X ... E) ρ_0)), then jumping to the body @(qil E)
in an environment and store that binds @(qil (X ...)) to the
dereference of @(qil (V ...)).  The @(qil deref) and @(qil bind)
metafunctions are straightforward:


@(metafunction-pict-style 'left-right/vertical-side-conditions)

@(centered (render-metafunctions deref bind))

The metafunctions @(qil extend-env) and @(qil extend-sto) have
the usual meaning.  We assume that @(qil (alloc σ X)) produces
some location @(qil A) not in @(qil σ).

A let redution @(qil (let X = D in E)) 
reduces @(qil D) and binds the results to @(qil X)
then jumps to the body of the let, @(qil E).  The work
of reducing and binding is done by @(qil push), which
relies on @(qil reduce) to contract @(qil D)-redexes:

@(centered (render-metafunctions push reduce))


The @(qil ∆) function interprets primitives in the way you would expect.
On quirk is that @(qil =) is interpreted as a function that returns @(qil 0)
for true and @(qil 1) for a false.

A recursive definition recurively binds a set of variables to (potentially
self- or mutually-referential) values.  The cyclic binding structure
is created by @(qil recbind):

@(centered (render-metafunction recbind))
which uses @(qil alloc*), @(qil extend-env*), and @(qil extend-sto*);
the @emph{n}-ary extensions of 
@(qil alloc), @(qil extend-env), and @(qil extend-sto).

Finally, a switch is reduced by dereferencing the value on which
to branch to obtain a constant, then jumping to the branch
that matches that constant.

@section[#:tag "abstract-semantics"]{An abstractable interpreter for Coq IL}

