open Types

val subst : 'a -> 'a -> 'a -> 'a

val subst_atom_in_constr : atom -> atom -> constr -> constr

val subst_var_in_constr : var -> term -> constr -> constr

val subst_atom_in_kind : atom -> atom -> kind -> kind

val subst_var_in_kind : var -> var -> kind -> kind
