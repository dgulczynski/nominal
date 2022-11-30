open Proof
open ProofEnv
open ProverInternals
open Types

val proof : formula env -> formula -> prover_state

val intro : string -> tactic

val apply : formula -> tactic

val apply_thm : proof -> tactic

val apply_assm : string -> tactic

val ex_falso : tactic

val truth : tactic

val qed : prover_state -> proof
