open Types
open Permutation
open Common
open SubstitutionInternal

type solver_constr =
  | SC_Fresh of atom * term
  | SC_Eq of term * term
  | SC_Shape of shape * shape
  | SC_Subshape of shape * shape
  | SC_AtomEq of atom * permuted_atom
  | SC_AtomNeq of atom * permuted_atom
  | SC_Symbol of shape

let ( #: ) a t = SC_Fresh (a, t)

let ( =: ) t1 t2 = SC_Eq (t1, t2)

let ( =~: ) t1 t2 = SC_Shape (t1, t2)

let ( <: ) t1 t2 = SC_Subshape (t1, t2)

let ( ==: ) a alpha = SC_AtomEq (a, alpha)

let ( =/=: ) a alpha = SC_AtomNeq (a, alpha)

let symbol t = SC_Symbol t

let from_constr = function
  | C_Fresh (a, term) -> SC_Fresh (a, term)
  | C_Eq (t1, t2) -> SC_Eq (t1, t2)
  | C_Shape (t1, t2) -> SC_Shape (shape_of_term t1, shape_of_term t2)
  | C_Subshape (t1, t2) -> SC_Subshape (shape_of_term t1, shape_of_term t2)
  | C_AtomEq (a, alpha) -> SC_AtomEq (a, alpha)
  | C_AtomNeq (a, alpha) -> SC_AtomNeq (a, alpha)
  | C_Symbol t -> SC_Symbol (shape_of_term t)

let subst_in_solver_constr sub = function
  | SC_Fresh (a, t) -> (
    match sub_atom sub a with
    | {perm= pi; symb= a} -> SC_Fresh (a, permute_term (reverse pi) $ subst_in_term sub t) )
  | SC_Eq (t1, t2) -> SC_Eq (subst_in_term sub t1, subst_in_term sub t2)
  | SC_Shape (s1, s2) -> SC_Shape (subst_in_shape sub s1, subst_in_shape sub s2)
  | SC_Subshape (s1, s2) -> SC_Subshape (subst_in_shape sub s1, subst_in_shape sub s2)
  | SC_AtomEq (a, alpha) -> (
    match sub_atom sub a with
    | {perm= pi; symb= a} -> SC_AtomEq (a, permute (reverse pi) $ sub_perm_atom sub alpha) )
  | SC_AtomNeq (a, alpha) -> (
    match sub_atom sub a with
    | {perm= pi; symb= a} -> SC_AtomNeq (a, permute (reverse pi) $ sub_perm_atom sub alpha) )
  | SC_Symbol t -> SC_Symbol (subst_in_shape sub t)

let subst_atom_in_solver_constr = subst_in_solver_constr %% mk_atom_subst

let subst_var_in_solver_constr = subst_in_solver_constr %% mk_var_subst
