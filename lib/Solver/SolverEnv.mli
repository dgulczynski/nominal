open Types
open SolverTypes

(** [SolverEnv] is the environment in which we keep assumptions of [Solver] that are irreducible
    (subset of [constr]s). *)

type t

val empty : t

val add_fresh : atom -> var -> t -> t
(** [add_fresh env a x] adds assumption [a # x] to [env] *)

val add_neq : atom -> atom -> t -> t option
(** [add_neq env a1 a2] adds assumption [a1 =/= a2] to [env], returns [None] if [a1 = a2] *)

val add_symbol : var -> t -> t option
(** [add_symbol x] adds assumption [symbol? x] to [env], returns [None] if exists [t] s.t. [t < x] *)

val is_fresh : t -> atom -> var -> bool
(** [is_neq env a1 a2] returns [true] iff there is assumption [a # x] in [env] *)

val is_neq : t -> atom -> atom -> bool
(** [is_neq env a1 a2] returns [true] iff there is assumption [a1 =/= a2] in [env] *)

val is_symbol : t -> var -> bool
(** [is_symbol x] returns [true] iff there is assumption [symbol? x] in [env] *)

val subst_atom : t -> atom -> atom -> t option
(** [subst_atom env a1 a2] performs substitution [{a1 -> a2}] over all assumptions in [env]
    , returns [None] if we have an assumption [a1 =/= a2], [Some env'] otherwise. *)

val subst_var : t -> var -> term -> (t * solver_constr list) option
(** [subst_var env x t] performs substitution [x -> t] over all assumptions in [env], returns [None]
    if [occurs_check env x t], [Some (env', env_assms)] otherwise, where [env_assms] is a list
    assumptions that may not be irreducible anymore and thus are extracted from [env']. *)

val set_var_shape : t -> var -> shape -> (t * solver_constr list) option

val add_same_shape : t -> var -> var -> (t * solver_constr list) option
(** [add_same_shape env x1 x2] adds an assumption [x1 ~ x2] to [env], returns [None] if
    other (sub)shape assumptions contradict it, otherwise [Some env'] *)

val are_same_shape : t -> var -> var -> bool
(** [are_same_shape env x1 x2] returns [true] iff we have an assumption [x1 ~ x2] *)

val add_subshape : t -> shape -> var -> (t * solver_constr list) option
(** [add_subshape env t x] adds an assumption [t < x] to [env], returns [None] if [occurs_check env x t], otherwise [Some env'] *)

val get_shape : t -> var -> shape option
(** [get_shape env x] returns optional shape [s] s.t. we have assumption [x ~ s] *)

val get_subshapes : t -> var -> shape list
(** [get_subshapes env x] returns a list of terms [t_0, ..., t_n] such that we have assumptions [t_i < x] *)

val occurs_check : t -> var -> shape -> bool
(** [occurs_check env x t] is a recursive procedure that checks whether [x] occurs syntatically in
    [t], and for each variable [y] occuring syntatically in [t] it checks if [x] occurs in any [t']
    such that we have an assumption [t' < y] *)

val string_of : t -> string
