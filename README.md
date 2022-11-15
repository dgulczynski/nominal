# nominal
This is repository of my master thesis concerning domain logic for reasoning about terms with binding of variables (polish title: Logika dziedzinowa do wnioskowania o termach z wiązaniem zmiennych).
Code and thesis text is still under development.

# Usage
Run via command: `dune exec nominal`, try it yourself with via `dune utop`, or check that examples are still working via `dune test`.

# Features / TODO list
- [x] Solver, testing wether $c_1, ..., c_n \vdash c$
- [x] Kind checker for formulas $\Gamma \vdash \phi : k$
- [ ] Judgement $\Delta; \Gamma \vdash \phi$
- [ ] HOL-like proof assistant
- [ ] Thesis text

# Libraries used
- [Angstrom](https://opam.ocaml.org/packages/angstrom/) - parser combinator library