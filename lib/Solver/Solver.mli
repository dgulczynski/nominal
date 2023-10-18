open Types

val ( |-: ) : constr list -> constr -> bool
(** [ cs |-: c] invokes the Solver: [[]; cs |- c]*)

val ( ||-: ) : constr -> bool
(** [ cs ||-: c] is [[] |-: c]*)

val absurd : constr
(** [absurd] is constraint that can be solved only with contradictory assumptions *)
