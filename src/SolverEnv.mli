open Types

module SolverEnv : sig
  type t

  val empty : t

  val add_fresh : t -> atom -> var -> t

  val add_neq : t -> atom -> atom -> t option

  val is_fresh : t -> atom -> var -> bool

  val is_neq : t -> atom -> atom -> bool

  val subst_atom : t -> atom -> atom -> t option

  val string_of : t -> string
end
