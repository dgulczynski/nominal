open Types

val syntactic_occurs_check : var -> term -> bool

val free_vars_of_term : term -> var list

val fresh : unit -> int

val fresh_var : unit -> var

val fresh_atom : unit -> atom

val fresh_fvar : unit -> fvar

val shape_of_term : term -> shape

val term_of_shape : shape -> term * (var * var) list
(** [term_of_shape s] returns [t] (which shape is the same as [s] up to alpha-equivalence) and [vs]
    (mapping from the [s] variables to generated fresh variables of [t]) *)

val fix_kind : var -> var -> string -> kind -> kind
(** [fix_kind x y k] returns [forall y. [y < x] => k{y/x}], the kind of [X] in [fix X(x) in f:k]*)

val fix_binder : string -> int -> var -> var -> string -> kind -> fvar_binder
(** [fix_binder fix_name fix_rep x y k] returns [FV_Bind(fix_name, fix_rep, fix_k)]
    where [fix_k = forall y. [y < x] => k{y/x}] *)

val fix : string -> int -> var -> string -> var -> string -> kind -> formula -> formula
(** [fix fix_name fix_rep x y k] returns [F_Fix(fix, x, k, k) = `fix x(fix_name) in f:k`]
    where [fix = fix_binder fix_name fix_rep x y k] *)

val free_names_of_formula : formula -> int list

val free_names_of_constr : constr -> int list

val atom_binder_to_binder : atom_binder -> binder

val var_binder_to_binder : var_binder -> binder

val fvar_binder_to_binder : fvar_binder -> binder

val bind_by_rep : int -> bound_env -> binder option

val bind_by_name : string -> bound_env -> binder option
