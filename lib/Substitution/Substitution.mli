open Types

val shape_of_term : term -> shape

val term_of_shape : shape -> term * (var * var) list
(** [term_of_shape s] returns [t] (which shape is the same as [s] up to alpha-equivalence) and [vs]
    (mapping from the [s] variables to generated fresh variables of [t]) *)

val subst_atom_in_term : atom -> permuted_atom -> term -> term

val subst_var_in_term : var -> term -> term -> term

val subst_atom_in_constr : atom -> permuted_atom -> constr -> constr

val subst_var_in_constr : var -> term -> constr -> constr

val subst_atom_in_kind : atom -> permuted_atom -> kind -> kind

val subst_var_in_kind : var -> term -> kind -> kind

val subst_atom_in_formula : atom -> permuted_atom -> formula -> formula

val ( |-> ) : atom -> permuted_atom -> formula -> formula

val subst_var_in_formula : var -> term -> formula -> formula

val ( |=> ) : var -> term -> formula -> formula

val subst_fvar_in_formula : fvar -> formula -> formula -> formula

val ( |==> ) : fvar -> formula -> formula -> formula

val subst_var_in_shape : var -> shape -> shape -> shape

val instantiate_atom : formula -> atom_binder * formula

val instantiate_var : formula -> var_binder * formula
