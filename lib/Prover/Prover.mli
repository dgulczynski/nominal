open Proof
open ProverGoal
open ProverInternals
open Types

val proof : goal_env -> formula -> prover_state

val intro : tactic

val intros : string list -> tactic

val apply : formula -> tactic

val apply_thm : proof -> tactic

val apply_thm_specialized : proof -> string list -> tactic

val apply_assm : string -> tactic

val apply_assm_specialized : string -> string list -> tactic

val by_solver : tactic

val ex_falso : tactic

val qed : prover_state -> proof

val generalize : string -> tactic

val exists : string -> tactic

val exists' : string list -> tactic

val destruct_assm : string -> tactic

val destruct_assm' : string -> string list -> tactic

val destruct_goal : tactic

val destruct_goal' : int -> tactic

val case : string -> tactic

val by_induction : string -> string -> tactic

val step : int -> tactic

val subst : string -> string -> tactic

val intros' : string list -> tactic

val add_assumption_thm : string -> proof -> tactic

val add_assumption_thm_specialized : string -> proof -> string list -> tactic

val specialize_assm : string -> string -> string list -> tactic

val apply_in_assm : string -> string -> tactic
