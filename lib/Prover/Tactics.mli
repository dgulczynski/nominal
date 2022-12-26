open ProverGoal
open ProverInternals
open Types

val apply_parse : string -> tactic

val add_assumption : string -> formula -> tactic

val add_assumption_parse : string -> string -> tactic

val add_constr : constr -> tactic

val add_constr_parse : string -> tactic

val assumption : tactic

val contradiction : tactic

val intros : string list -> tactic

val proof' : goal -> prover_state

val repeat : tactic -> tactic

val trivial : tactic

val try_tactic : tactic -> tactic
