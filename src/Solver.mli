open Types

val solve : constr -> bool
(** [solve c] returns [[]; [] |- c] *)

val solve_with_assumptions : constr list -> constr -> bool
(** [solve_with_assumptions cs] returns [[]; cs |- c] *)
