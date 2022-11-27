open IncProof
open ProofContext
open Types

type prover_state

type tactic = prover_state -> prover_state

val find_goal_in_ctx : incproof -> proof_context -> prover_state

val goal : prover_state -> goal

val context : prover_state -> proof_context

val goal_env : prover_state -> goal_env

val goal_formula : prover_state -> formula

val lookup : goal_env -> string -> formula

val apply_internal : incproof -> string option -> tactic

val unfinished : goal -> proof_context -> prover_state

val finish : prover_state -> incproof