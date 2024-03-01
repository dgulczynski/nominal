open Types

exception ProofException of string

type spec = SpecAtom of permuted_atom * formula | SpecTerm of term * formula | SpecForm of formula * formula

type formula_mapping = {bind: fvar_binder; body: formula}

type mapping = formula_mapping list
