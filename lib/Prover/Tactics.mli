open ProverGoal
open ProverInternals

val assumption : tactic

val contradiction : tactic

val intros : string list -> tactic

val proof' : goal -> prover_state

val repeat : tactic -> tactic

val trivial : tactic

val try_tactic : tactic -> tactic
