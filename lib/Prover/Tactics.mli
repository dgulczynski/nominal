open ProverGoal
open ProverInternals
open Types

val apply_parse : string -> tactic

val add_assumption_parse : string -> string -> tactic

val add_constr : constr -> tactic

val add_constr_parse : string -> tactic

val assumption : tactic

val contradiction : tactic

val proof' : goal -> prover_state

val repeat : tactic -> tactic

val trivial : tactic

val try_tactic : tactic -> tactic

val left : tactic

val right : tactic

val compute : tactic

val discriminate : tactic

val intro' : tactic

val compare_atoms : string -> string -> tactic

val get_fresh_atom : string -> string -> tactic

val inverse_term : string -> tactic
