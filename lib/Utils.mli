open Types

val fix_kind : var -> var -> kind -> kind
(** [fix_kind x y k] returns [forall y. [y < x] => k{y/x}], the be kind of [X] in [fix x(X) in f:k]*)

val fix_binder : string -> int -> var -> var -> kind -> fvar_binder
(** [fix_binder fix_name fix_rep x y k] returns [FV_Bind(fix_name, fix_rep, fix_k)]
    where [fix_k = forall y. [y < x] => k{y/x}] *)

val fix : string -> int -> var -> var -> kind -> formula -> formula
(** [fix fix_name fix_rep x y k] returns [F_Fix(fix, x, k, k) = `fix x(fix_name) in f:k`]
    where [fix = fix_binder fix_name fix_rep x y k] *)
