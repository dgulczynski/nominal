type atom = A of string

type var = V of string

type symbol = string

type 'a permutation = (('a, 'a) permuted * ('a, 'a) permuted) list

and ('a, 'x) permuted = Just of 'x | Permuted of 'a permutation * 'x

type permuted_atom = (atom, atom) permuted

type permuted_var = (atom, var) permuted

type term =
  | Var  of permuted_var
  | Atom of permuted_atom
  | Lam  of permuted_atom * term
  | App  of term * term
  | Fun  of symbol

type shape =
  | SVar  of var
  | SAtom
  | SLam  of shape
  | SApp  of shape * shape
  | SFun  of symbol

type constr =
  | Fresh    of atom * term
  | Eq       of term * term
  | Neq      of term * term
  | Shape    of term * term
  | Subshape of term * term
  | AtomEq   of atom * permuted_atom
  | AtomNeq  of atom * permuted_atom

let ( #: ) a t = Fresh (a, t)

let ( =: ) t1 t2 = Eq (t1, t2)

let ( !=: ) t1 t2 = Neq (t1, t2)

let ( ~: ) t1 t2 = Shape (t1, t2)

let ( <: ) t1 t2 = Subshape (t1, t2)

let ( ==: ) a alpha = AtomEq (a, alpha)

let ( !==: ) a alpha = AtomNeq (a, alpha)
