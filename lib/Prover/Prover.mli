open Proof
open ProverGoal
open ProverInternals
open Types

val proof : goal_env -> formula -> prover_state

val intro : string -> tactic

val intro_constr : tactic

val apply : formula -> tactic

val apply_thm : proof -> tactic

val apply_assm : string -> tactic

val by_solver : tactic

val ex_falso : tactic

val truth : tactic

val qed : prover_state -> proof
