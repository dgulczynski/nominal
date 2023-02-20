open Types
open ProofEnv

type proof_env = formula env

type judgement = proof_env * formula

type proof = private
  | P_Ax             of judgement
  | P_Intro          of judgement * proof
  | P_Apply          of judgement * proof * proof
  | P_ConstrApply    of judgement * proof * proof
  | P_ConstrAndElim  of judgement * proof * proof
  | P_SpecializeAtom of judgement * atom * proof
  | P_SpecializeTerm of judgement * term * proof
  | P_Witness        of judgement * proof * proof
  | P_AndIntro       of judgement * proof list
  | P_AndElim        of judgement * proof
  | P_OrElim         of judgement * proof list
  | P_ExFalso        of judgement * proof

val label : proof -> formula

val env : proof -> proof_env

val judgement : proof -> judgement

val axiom : identifier_env -> formula -> proof

val imp_i : formula -> proof -> proof

val imp_e : proof -> proof -> proof

val bot_e : formula -> proof -> proof

val constr_i : proof_env -> constr -> proof

val constr_imp_i : constr -> proof -> proof

val constr_imp_e : proof -> proof -> proof

val constr_and_i : constr -> proof -> proof

val constr_and_e : proof -> proof -> proof

val forall_atom_i : atom -> proof -> proof

val forall_atom_e : atom -> proof -> proof

val forall_term_i : var -> proof -> proof

val forall_term_e : term -> proof -> proof

val exists_atom_i : atom -> atom -> formula -> proof -> proof
(** [exists_atom_i a b f p] is a proof of [exists a : atom. f] where [b] is the witness and [p] is proof of [(a |-> b) f]*)

val exists_term_i : var -> term -> formula -> proof -> proof
(** [exists_term_i x t f p] is a proof of [exists x : term. f] where [t] is the witness and [p] is proof of [(x |=> t) f]*)

val exist_e : proof -> proof -> proof

val and_i : proof list -> proof

val and_e : formula -> proof -> proof

val or_i : formula list -> proof -> proof

val or_e : proof -> proof list -> proof

val induction_e : var -> var -> proof -> proof
