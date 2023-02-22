open Permutation

type atom = A of string

type var = V of string

type permuted_atom = (atom, atom) permuted

type permuted_var = (atom, var) permuted

type term =
  | T_Var  of permuted_var
  | T_Atom of permuted_atom
  | T_Lam  of permuted_atom * term
  | T_App  of term * term
  | T_Fun  of string

type shape = S_Var of var | S_Atom | S_Lam of shape | S_App of shape * shape | S_Fun of string

type constr =
  | C_Fresh    of atom * term
  | C_Eq       of term * term
  | C_Shape    of term * term
  | C_Subshape of term * term
  | C_AtomEq   of atom * permuted_atom
  | C_AtomNeq  of atom * permuted_atom

let ( #: ) a t = C_Fresh (a, t)

let ( =: ) t1 t2 = C_Eq (t1, t2)

let ( =~: ) t1 t2 = C_Shape (t1, t2)

let ( <: ) t1 t2 = C_Subshape (t1, t2)

let ( ==: ) a alpha = C_AtomEq (a, alpha)

let ( =/=: ) a alpha = C_AtomNeq (a, alpha)

type kind =
  | K_Prop
  | K_Arrow      of kind * kind
  | K_ForallTerm of var * kind
  | K_ForallAtom of atom * kind
  | K_Constr     of constr * kind

type fvar_internal = int

type fvar = FV of fvar_internal

type fvar_binder = FV_Bind of string * fvar_internal * kind

type formula =
  | F_Bot
  | F_Top
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
  | F_Fun        of fvar_binder * formula
  | F_App        of formula * formula
  | F_FunTerm    of var * formula
  | F_AppTerm    of formula * term
  | F_FunAtom    of atom * formula
  | F_AppAtom    of formula * atom
  | F_Fix        of fvar_binder * var * kind * formula

type identifier_kind = K_Atom | K_Var | K_Func | K_FVar of fvar_internal * kind

type identifier = string * identifier_kind

type identifier_env = identifier list
