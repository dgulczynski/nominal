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

val ( #: ) : atom -> term -> constr

val ( =: ) : term -> term -> constr

val ( ~: ) : term -> term -> constr

val ( <: ) : term -> term -> constr

val ( ==: ) : atom -> permuted_atom -> constr

val ( =/=: ) : atom -> permuted_atom -> constr

type kind =
  | Prop
  | Arrow      of kind * kind
  | ForallTerm of var * kind
  | ForallAtom of atom * kind
  | Constr     of constr * kind

type fvar = var

type formula =
  | F_Var        of fvar
  | F_Constr     of constr
  | F_And        of formula * formula
  | F_Or         of formula * formula
  | F_Impl       of formula * formula
  | F_Bot
  | F_ForallTerm of var * formula
  | F_ExistsTerm of var * formula
  | F_ForallAtom of atom * formula
  | F_ExistsAtom of atom * formula
  | F_ConstrAnd  of constr * formula
  | F_ConstrImpl of constr * formula
  | F_Fun        of fvar * formula
  | F_App        of formula * formula
  | F_FunTerm    of var * formula
  | F_AppTerm    of formula * term
  | F_FunAtom    of atom * formula
  | F_AppAtom    of formula * permuted_atom
  | F_Fix        of fvar * fvar * formula
