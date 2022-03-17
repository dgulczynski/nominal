open Permutation

type atom = A of string

type var = V of string

type symbol = string

type permuted_atom = (atom, atom) permuted

type permuted_var = (atom, var) permuted

type term =
  | T_Var  of permuted_var
  | T_Atom of permuted_atom
  | T_Lam  of permuted_atom * term
  | T_App  of term * term
  | T_Fun  of symbol

type shape = S_Var of var | S_Atom | S_Lam of shape | S_App of shape * shape | S_Fun of symbol

type constr =
  | C_Fresh    of atom * term
  | C_Eq       of term * term
  | C_Shape    of term * term
  | C_Subshape of term * term
  | C_AtomEq   of atom * permuted_atom
  | C_AtomNeq  of atom * permuted_atom

val ( #: ) : atom -> term -> constr

val ( =: ) : term -> term -> constr

val ( =~: ) : term -> term -> constr

val ( <: ) : term -> term -> constr

val ( ==: ) : atom -> permuted_atom -> constr

val ( =/=: ) : atom -> permuted_atom -> constr

type kind =
  | K_Prop
  | K_Arrow      of kind * kind
  | K_ForallTerm of var * kind
  | K_ForallAtom of atom * kind
  | K_Constr     of constr * kind

type fvar = FV of string

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
  | F_Fun        of fvar * kind * formula
  | F_App        of formula * formula
  | F_FunTerm    of var * formula
  | F_AppTerm    of formula * term
  | F_FunAtom    of atom * formula
  | F_AppAtom    of formula * atom
  | F_Fix        of fvar * var * formula
