open Types
open Proof
open ProverInternals

val assumption : tactic

val contradiction : tactic

val intros : string list -> tactic

val proof' : proof_env * formula -> prover_state

val trivial : tactic

val try_tactic : tactic -> tactic
