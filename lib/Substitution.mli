open Types

val subst : 'a -> 'a -> 'a -> 'a
(** [subst a b c = if c = a then b else c]*)

val subst_atom_in_term : atom -> atom -> term -> term

val subst_var_in_term : var -> term -> term -> term

val subst_atom_in_constr : atom -> atom -> constr -> constr

val subst_var_in_constr : var -> term -> constr -> constr

val subst_atom_in_kind : atom -> atom -> kind -> kind

val subst_var_in_kind : var -> term -> kind -> kind

val subst_atom_in_formula : atom -> atom -> formula -> formula

val subst_var_in_formula : var -> term -> formula -> formula

val subst_var_in_shape : var -> shape -> shape -> shape

val fix_kind : var -> var -> kind -> kind
(** [fix_kind x y k] returns [forall y. [y < x] => k{y/x}], the be kind of [X] in [fix x(X) in f:k]*)

val fix_binder : string -> int -> var -> var -> kind -> fvar_binder
(** [fix_binder fix_name fix_rep x y k] returns [FV_Bind(fix_name, fix_rep, fix_k)]
    where [fix_k = forall y. [y < x] => k{y/x}] *)

val fix : string -> int -> var -> var -> kind -> formula -> formula
(** [fix fix_name fix_rep x y k] returns [F_Fix(fix, x, k, k) = `fix x(fix_name) in f:k`]
    where [fix = fix_binder fix_name fix_rep x y k] *)