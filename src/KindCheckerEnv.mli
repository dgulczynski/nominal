open Types

module KindCheckerEnv : sig
  type t

  val empty : t

  val add_constr : t -> constr -> t

  val mem_constr : t -> constr -> bool

  val constraints_of : t -> constr list

  val string_of : t -> string
end
