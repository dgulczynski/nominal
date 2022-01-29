open Permutation

type atom = A of string

type var = V of string

type symbol = string

type permuted_atom = (atom, atom) permuted

type permuted_var = (atom, var) permuted

type term =
  | Var  of permuted_var
  | Atom of permuted_atom
  | Lam  of permuted_atom * term
  | App  of term * term
  | Fun  of symbol

type shape = SVar of var | SAtom | SLam of shape | SApp of shape * shape | SFun of symbol

type constr =
  | Fresh    of atom * term
  | Eq       of term * term
  | Shape    of term * term
  | Subshape of term * term
  | AtomEq   of atom * permuted_atom
  | AtomNeq  of atom * permuted_atom

let ( #: ) a t = Fresh (a, t)

let ( =: ) t1 t2 = Eq (t1, t2)

let ( ~: ) t1 t2 = Shape (t1, t2)

let ( <: ) t1 t2 = Subshape (t1, t2)

let ( ==: ) a alpha = AtomEq (a, alpha)

let ( =/=: ) a alpha = AtomNeq (a, alpha)

type kind =
  | K_Prop
  | K_Arrow      of kind * kind
  | K_ForallTerm of var * kind
  | K_ForallAtom of atom * kind
  | K_Constr     of constr * kind

type fvar = var

type formula =
  | F_Bot
  | F_Constr     of constr
  | F_And        of formula list
  | F_Or         of formula list
  | F_Impl       of formula * formula
  | F_ForallTerm of var * formula
  | F_ForallAtom of atom * formula
  | F_ExistsTerm of var * formula
  | F_ExistsAtom of atom * formula
  | F_ConstrAnd  of constr * formula
  | F_ConstrImpl of constr * formula
  | F_Var        of fvar
  | F_Fun        of fvar * formula
  | F_App        of formula * formula
  | F_FunTerm    of var * formula
  | F_AppTerm    of formula * term
  | F_FunAtom    of atom * formula
  | F_AppAtom    of formula * permuted_atom
  | F_Fix        of fvar * fvar * formula
