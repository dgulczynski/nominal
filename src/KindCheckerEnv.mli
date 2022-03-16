open Types

type t

val empty : t

val map_var : t -> var -> var -> t

val find_var : t -> var -> var option

val map_atom : t -> atom -> atom -> t

val find_atom : t -> atom -> atom option

val map_fvar : t -> fvar -> kind -> t

val find_fvar : t -> fvar -> kind option

val add_constr : t -> constr -> t

val mem_constr : t -> constr -> bool

val constraints_of : t -> constr list

val string_of : t -> string
