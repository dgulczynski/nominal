open Types
open ProofEnv

type proof_env = formula env

type judgement = proof_env * formula

type proof = private
  | P_Ax             of judgement
  | P_Intro          of judgement * proof
  | P_Apply          of judgement * proof * proof
  | P_ConstrIntro    of judgement * proof
  | P_ConstrApply    of judgement * proof * proof
  | P_SpecializeAtom of judgement * atom * proof
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

val forall_atom_i : atom -> proof -> proof

val forall_atom_e : atom -> proof -> proof
