open Proof
open ProverGoal
open ProverInternals
open Types

val proof : goal_env -> formula -> prover_state

val intro : tactic

val intro_named : string -> tactic

val apply : formula -> tactic

val apply_thm : proof -> tactic

val apply_assm : string -> tactic

val by_solver : tactic

val ex_falso : tactic

val truth : tactic

val qed : prover_state -> proof

val generalize : string -> tactic
