open Types
open PrettyPrintingCore
open PrettyPrintingTerm

let pretty_constr = function
  | C_Fresh (a, t) -> pretty_binop_unbreaking (pretty_atom a) "#" (pretty_term t)
  | C_AtomEq (a, b) -> pretty_binop_unbreaking (pretty_atom a) "==" (pretty_atom_permuted b)
  | C_AtomNeq (a, b) -> pretty_binop_unbreaking (pretty_atom a) "=/=" (pretty_atom_permuted b)
  | C_Eq (t1, t2) -> pretty_binop_unbreaking (pretty_term t1) "=" (pretty_term t2)
  | C_Shape (t1, t2) -> pretty_binop_unbreaking (pretty_term t1) "~" (pretty_term t2)
  | C_Subshape (t1, t2) -> pretty_binop_unbreaking (pretty_term t1) "<" (pretty_term t2)
  | C_Symbol t -> pretty_unop "symbol" (pretty_term t)
