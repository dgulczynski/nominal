open Types

(** [SolverEnv] is the environment in which we keep assumptions of [Solver] that are irreducible
    (subset of [constr]s). *)

type t

val empty : t

val add_fresh : t -> atom -> var -> t
(** [add_fresh env a x] adds assumption [a #: var x] to [env] *)

val add_neq : t -> atom -> atom -> t option
(** [add_neq env a1 a2] adds assumption [atom a1 =/=: atom a2] to [env], returns [None] if [a1 =
    a2] *)

val is_fresh : t -> atom -> var -> bool
(** [is_neq env a1 a2] returns [true] iff there is assumption [a #: var x] in [env] *)

val is_neq : t -> atom -> atom -> bool
(** [is_neq env a1 a2] returns [true] iff there is assumption [atom a1 =/=: atom a2] in [env] *)

val subst_atom : t -> atom -> atom -> t option
(** [subst_atom env a1 a2] performs substitution [{a2/a1}] over all assumptions in [env], returns
    [None] if we have an assumption [atom a1 =/=: atom a2], [Some env'] otherwise. *)

val subst_var : t -> var -> term -> (t * constr list) option
(** [subst_var env x t] performs substitution [{t/x}] over all assumptions in [env], returns [None]
    if [occurs_check env x t], [Some (env', env_assms)] otherwise, where [env_assms] is a list
    assumptions that may not be irreducible anymore and thus are extracted from [env']. *)

val add_same_shape : t -> var -> var -> t option
(** [add_same_shape env x1 x2] adds an assumption [var x1 =~: var x2] to [env], returns [None] if if
    other (sub)shape assumptions contradicts it, otherwise [Some env'] *)

val are_same_shape : t -> var -> var -> bool
(** [are_same_shape env x1 x2] returns [true] iff we have an assumption [var x1 =~: var x2] *)

val add_subshape : t -> term -> var -> t option
(** [add_subshape env t x] adds an assumption [t <: var x] to [env], returns [None] if [occurs_check
    env x t], otherwise [Some env'] *)

val get_shapes : t -> var -> var list
(** [get_shapes env x] returns a list of variables [y_i, ..., y_n] such that we have assumptions
    [var y_i =~: var x] *)

val get_subshapes : t -> var -> term list
(** [get_subshapes env x] returns a list of terms [t_0, ..., t_n] such that we have assumptions [t_i
    <: var x] *)

val occurs_check : t -> var -> term -> bool
(** [occurs_check env x t] is a recursive procedure that checks whether [x] occurs syntatically in
    [t], and for each variable [y] occuring syntatically in [t] it checks if [x] occurs in any [t']
    such that we have an assumption [t' <: y] *)

val string_of : t -> string
