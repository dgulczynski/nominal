open Types

val solve : constr -> bool
(** [solve c] returns [[]; [] |- c] *)

val solve_with_assumptions : constr list -> constr -> bool
(** [solve_with_assumptions cs c] returns [[]; cs |- c] *)

val ( |-: ) : constr list -> constr -> bool
(** [ cs |-: c] is [solve_with_assumptions cs c], meaning [[]; cs |- c]*)
