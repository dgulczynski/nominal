open Types
open Permutation
open Common
open SubstitutionInternal

let rec shape_of_term = function
  | T_Var {symb= x; _} -> S_Var x
  | T_Atom _ -> S_Atom
  | T_Lam (_, t) -> S_Lam (shape_of_term t)
  | T_App (t1, t2) -> S_App (shape_of_term t1, shape_of_term t2)
  | T_Fun f -> S_Fun f

let rec term_of_shape = function
  | S_Var x ->
    let y = fresh_var () in
    (var y, [(x, y)])
  | S_Atom -> (atom $ fresh_atom (), [])
  | S_Lam s ->
    let t, vs = term_of_shape s in
    (T_Lam (pure $ fresh_atom (), t), vs)
  | S_App (s1, s2) ->
    let t1, vs1 = term_of_shape s1 and t2, vs2 = term_of_shape s2 in
    (T_App (t1, t2), vs1 @ vs2)
  | S_Fun f -> (T_Fun f, [])

let subst_atom_in_term = subst_in_term %% mk_atom_subst

let subst_var_in_term = subst_in_term %% mk_var_subst

let subst_var_in_shape = subst_in_shape %% mk_var_shape_subst

let subst_atom_in_constr = subst_in_constr %% mk_atom_subst

let subst_var_in_constr = subst_in_constr %% mk_var_subst

let subst_atom_in_kind = subst_in_kind %% mk_atom_subst

let subst_var_in_kind = subst_in_kind %% mk_var_subst

let subst_atom_in_formula = subst_in_formula %% mk_atom_subst

let subst_var_in_formula = subst_in_formula %% mk_var_subst

let subst_fvar_in_formula = subst_in_formula %% mk_fvar_subst

let ( |-> ) = subst_atom_in_formula

let ( |=> ) = subst_var_in_formula

let ( |==> ) = subst_fvar_in_formula

let instantiate_atom = instantiate_atom empty

let instantiate_var = instantiate_var empty
