open Types

type substitution

val empty : substitution

val sub_atom : substitution -> atom -> permuted_atom

val mk_atom_subst : atom -> permuted_atom -> substitution

val mk_var_subst : var -> term -> substitution

val mk_var_shape_subst : var -> shape -> substitution

val mk_fvar_subst : fvar -> formula -> substitution

val sub_perm_atom : substitution -> permuted_atom -> permuted_atom

val subst_in_term : substitution -> term -> term

val subst_in_constr : substitution -> constr -> constr

val subst_in_shape : substitution -> shape -> shape

val subst_in_kind : substitution -> kind -> kind

val subst_in_formula : substitution -> formula -> formula

val instantiate_atom : substitution -> formula -> atom_binder * formula

val instantiate_var : substitution -> formula -> var_binder * formula
