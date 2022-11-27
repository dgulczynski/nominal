open IncProof
open ProverInternals
open Types

val proof : formula list -> formula -> prover_state

val intro : string -> tactic

val apply : formula -> tactic

val apply_thm : incproof -> tactic

val apply_assm : string -> tactic

val ex_falso : tactic

val truth : tactic

val qed : prover_state -> incproof
