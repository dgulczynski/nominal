open Types

val subst : 'a -> 'a -> 'a -> 'a

val subst_atom_in_term : atom -> atom -> term -> term

val subst_var_in_term : var -> term -> term -> term

val subst_atom_in_constr : atom -> atom -> constr -> constr

val subst_var_in_constr : var -> term -> constr -> constr

val subst_atom_in_kind : atom -> atom -> kind -> kind

val subst_var_in_kind : var -> term -> kind -> kind

val subst_atom_in_formula : atom -> atom -> formula -> formula

val subst_var_in_formula : var -> term -> formula -> formula

val subst_var_in_shape : var -> shape -> shape -> shape
