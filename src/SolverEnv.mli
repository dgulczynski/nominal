open Types

(** [SolverEnv] is the environment in which we keep assumptions of [Solver] that are irreducible
    (subset of [constr]s). *)

type t

val empty : t

val add_fresh : t -> atom -> var -> t

val add_neq : t -> atom -> atom -> t option

val is_fresh : t -> atom -> var -> bool

val is_neq : t -> atom -> atom -> bool

val subst_atom : t -> atom -> atom -> t option

val subst_var : t -> var -> term -> (t * constr list) option

val add_same_shape : t -> var -> var -> t option

val are_same_shape : t -> var -> var -> bool

val add_subshape : t -> term -> var -> t option

val get_shapes : t -> var -> var list

val get_subshapes : t -> var -> term list

val occurs_check : t -> var -> term -> bool
(** [occurs_check env x t] is a recursive procedure that checks whether [x] occurs syntatically in
    [t], as well as for each variable [y] occuring in [t], it checks if [x] occurs in any [y'] that
    [y] is same shape with or if it occurs in any [t'] s.t. we have an assumption [t' <: y] *)

val string_of : t -> string
