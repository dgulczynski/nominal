open Prelude
open SubstitutionInternal

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
