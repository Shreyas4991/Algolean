# Algolean

Algolean is a library of algorithms and complexity theory, defined broadly to include much of the Algorithms and Complexity theory literature. It is written in the lightweight free monad version of what I call the "query-combinator" model. It currently consists of code that lies in several CSLib pull requests. The framework can encompass standard and custom models in algorithms theory, ranging from RAM and Turing machines, to circuits, and even niche models like the Robertson-Webb cake cutting model. The intent is to provide an all-encompassing framework of models and reductions between them. This framework forces formalizers to declare their basic operations and costs upfront and realizes complexity claims as purely structural consequences of the basic costs.

## Nomenclature
`Algolean` is a pun. It is intended to be read in two ways.
* "Algo" + "Lean" : A library of algorithms and complexity theory in lean
* "Algol" + "ean" (pronounced like "ene") : To pay homage to Algol which motivates a lot of modern algorithmic pseudocode, and whose simplicity this framework hopes to mimic (hence the "ene").

**Note**: I originally wrote the text below recently in leanprover/cslib#685 to help the maintainers understand my approach. I am borrowing it here to help those who come across this repository from other places.

## The Query Combinator Model : The basic idea

This is the original query-combinator model for algorithms theory within CSLib, first introduced in #201 and #275, and refined in #372 . Another, strictly later PR, #401, mimics this approach with minor implementation differences, which we do not think would help us. Below I explain the approach and attach my poster from the STOC'26 workshop "Can AI Do Theory" which succinctly summarizes it.

Algorithms exist in a variety of algorithmic models. These models are defined by the unit operations they care to count. For example:

The word-RAM model counts the number of RAM instructions such as word arithmetic, load, store, and boolean operations.
The cell probe model counts the number of memory cells read.
The cut-query model of graph algorithms counts the number of calls to the cut query.
Turing machines count the number of TM transitions.
The streaming model gets the next element of an input stream.
The LCA model queries a vertex of a graph to get its neighborhood structure.
Given any set of queries, these are sequentially combined using the same programmatic operations : conditionals, loops, procedure calls, recursion etc.

The query combinator approach parametrises a combinator language over the type of unit operations, which we treat as queries answered by an oracle. An algorithm in this approach is an abstract syntax tree, whose internal nodes are combinators, and whose leaf nodes are unit operations or pure operations.

## Our Implementation

We treat queries as values, specifically constructors of an inductive type. The inputs to a query are arguments of the constructor. The queries by themselves are uninterpreted atoms.
Models of a query type provide two functions evalQuery and time. The former provides the meaning of a query. The latter its cost. The cost type may be essentially any commutative monoid. We bundle costs and models together since these together define a computational model and we can speak of reductions between models using Progs.
Combinators: We re-use CSLib's FreeM, which are freer monads. We provide a suitable type abbreviation Prog. This provides a single combinator liftBind, which is a continuation, and a single leaf-node constructor pure. Since this happens to be a monad constructor, we get to reuse all of lean's combinators and constructions. This saves us the pain of reinventing substitution, procedure calls etc. This makes our framework more lightweight than a deeper embedding would allow.
Note: This is not necessarily the only possible combinator type. One could implement the IMP language for example. We choose this monadic approach for a few reasons listed further down.

## What this respository can accomplish:

Formalize algorithms at the right level of abstraction. A frontier paper needn't be out of reach because we haven't formalized all prior algorithms it relies on. We can formalize papers upto prior literature by treating those algorithms as queries. This lets us focus on the mathematical content of the paper we are formalizing.

It helps us formalize a hierarchy of models, and reduce them all the way down to basic models.

Query types can play the role of Abstract Data Types for data structures.

A range of algorithmic models can be formalized in one framework with one set of API lemmas.

We can mix models through reductions. So for instance we can define "uniform" circuit classes, since we can talk about TMs and circuits, all in one framework.

Prove lower bounds for models using a model uniform approach. As long as there are sufficiently many correct models of a query that produce different outputs on the same input, a Prog must call the query enough times to distinguish between them. So a sorting algorithm that sorts n items must deal with 
n
!
 different potential orders among these items.

## Why a monadic combinator and not a deeper embedding

This is a design decision. One can of course produce a deeper embedding by reinventing a combinator language, giving it a suitable memory model and restricting the non-query operations. This however comes with some trade-offs

Implementing a deeply embedded language is a non-trivial task. One has to reinvent the basic constructs, proofs of termination, recursion, variable binding, procedure calls, etc.
Choosing memory models and other implementation details is non-trivial and often beside the point of algorithms from the theory side.
If one is an algorithms theorist and wishes to rubber duck algorithms in lean, one usually wants to be able to write some operations they don't care about as pure operations.
Don't-care operations are fairly normal in the algorithms literature.
Why bundle evaluation and costs into models

Conceptually, a model is by definition a combination of its unit operations and their costs. For example, variants of RAM such as integer vs word ram and custom arithmetic models based on them. They support the same operations which evaluate the same way. They only differ in costs. These are meaningfully distinct models.

Query composition and reductions can be written in one place. Code for this exists already in Algolean. They are key to building the network of models which takes us from high level algorithms using one or more abstract ADTs for data structures to low level models. Not bundling them results in pointless repetition of the definitions and theorems of composition, reduction, and reduction of compositions of models.

## How can one guard against subversion

In general an algorithm is part of the spec. If someone writes a definition named heapsort and then proceeds to write mergeSort in the body of the declaration, of course they would get the right complexity upper bounds and correctness proofs. This alone suggests that checking the algorithmic pseudocode is essential.

One could insist on theorems that produce a hard input instance.

Using pure operations from existing library code. One can block this by requiring correctness proofs to have uniform correctness guarantees. This means, if a sorting algorithm is written with a cmpLE query, it must be correct against all possible models le of this query it a total order. A correct Prog gets no ordering relation upfront. Thus it cannot cheat against an adversarially provided le with a pure function. This of course doesn't hold if for example if you have a determinant query and there is only one valid unique model for this query.

Closely relevant poster : main.pdf

## Some attribution

This approach was partly inspired by a similar approach taken in the Agda DSL for synchronous hardware named PiWare by João Paulo Pizani Flor and Wouter Swierstra. There they parametrise a data type of circuit combinators with a cell library. We built on that idea but allowed algorithms to be expressed as ASTs over a set of basic operations. The goal was putting both basic and frontier algorithms within reach of formalization at a level of detail that algorithms theory papers actually use.

## Acknowledgements
For timing we build on top of the Writer monad `AddWriter` that was proposed in CSLib as the TimeM model by Sorrachai Yingchareonthawornchai and whose API was perfected by Eric Wieser. 

Further, Eric Wieser substantially assisted with the improvement of the implementation through extensive and detailed PR reviews. 

