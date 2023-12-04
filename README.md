# Domain-specific logic for terms with variable binding
This is the repository of my master thesis concerning domain-specific logic for
reasoning about terms with variable binding (polish title: Logika dziedzinowa do
wnioskowania o termach z wiązaniem zmiennych).

# Usage
Try it yourself with via `dune utop`, or see examples validate via `dune test`.

# Features
- Constraints solver
- Kind checker for formulas
- Proof constructors
- HOL-like proof assistant
- Parser and pretty-printer
- Thesis text

# Libraries used
- [angstrom](https://opam.ocaml.org/packages/angstrom/) - parser combinator library
- [easy-format](https://opam.ocaml.org/packages/easy-format/) - pretty printing library

# Abstract
In this work, we address a fundamental distinction between manual and
computer-based proof systems, emphasizing the challenge of maintaining precision
and transparency in handling variable binding. The common practice of making
unspoken assumptions in pen-and-paper proofs, particularly the use of the
imprecise notion of “sufficiently fresh names”, introduces potential pitfalls
when translating to formal and rigorous proof systems.

Nominal Logic, as introduced by Andrew M. Pitts, emerges as a promising
solution to bridge this gap, offering a first-order theory of names and binding.
This approach allows for the definition of essential concepts, including
alpha-equivalence, freshness, and variable binding, solely in terms of
name swapping rather than classical renaming.

Building upon Pitts’ work, we introduce a specialized variant of Nominal Logic,
where we define constraints - precise descriptors of syntactical properties -
and use them to reason about terms with variable binding.
We introduce “The Solver” - an algorithm for automated constraint resolution,
which forms the logical core of the constraints sublogic and acts as a middle
ground between human and computer provers. Layered on top of the constraints,
we define a higher-order logic with constraints embedded into propositional
formulas and relations.

Alongside this logic, we establish a proof system and a proof assistant
implemented in OCaml and inspired by HOL theorem provers. The integration of
these components forms a cohesive framework for the precise articulation of and
reasoning about complex syntactic properties. To demonstrate its potential for
reasoning within the programming languages world, we conduct proofs of classical
properties of simply typed lambda calculus using this framework.
