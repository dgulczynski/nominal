open IncProof
open IncProofContext
open ProverGoal
open Types

(** Type of in-progress proof of [Prover]. For ease of development it is defined here, but in future it will be abstract *)
type prover_state = S_Unfinished of {goal: goal; context: proof_context} | S_Finished of incproof

type tactic = prover_state -> prover_state

val find_goal_in_ctx : incproof -> proof_context -> prover_state

val goal : prover_state -> goal

val context : prover_state -> proof_context

val goal_env : prover_state -> goal_env

val goal_formula : prover_state -> formula

val lookup : goal_env -> string -> formula

val apply_internal : ?h_name:string -> incproof -> tactic

val unfinished : goal -> proof_context -> prover_state

val finish : prover_state -> incproof