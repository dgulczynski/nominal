open Types

type t

val empty : t

val add_fresh : t -> atom -> var -> t

val add_neq : t -> atom -> atom -> t option

val is_fresh : t -> atom -> var -> bool

val is_neq : t -> atom -> atom -> bool

val subst_atom : t -> atom -> atom -> t option

val subst_var : t -> var -> term -> t * constr list

val add_same_shape : t -> var -> var -> t * constr list

val are_same_shape : t -> var -> var -> bool

val add_subshape : t -> term -> var -> t option

val get_shapes : t -> var -> var list

val get_subshapes : t -> var -> term list

val occurs_check : t -> var -> term -> bool

val string_of : t -> string
