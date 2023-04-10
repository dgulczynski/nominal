open Types
open ProofEnv

type proof_env = formula env

type judgement = proof_env * formula

type proof = private
  | P_Ax             of judgement
  | P_Intro          of judgement * proof
  | P_Apply          of judgement * proof * proof
  | P_ConstrApply    of judgement * proof * proof
  | P_ConstrAndElim  of judgement * proof
  | P_SpecializeAtom of judgement * permuted_atom * proof
  | P_SpecializeTerm of judgement * term * proof
  | P_Witness        of judgement * proof * proof
  | P_AndIntro       of judgement * proof list
  | P_AndElim        of judgement * proof
  | P_OrElim         of judgement * proof list
  | P_Equivalent     of judgement * int * proof
  | P_Substitution   of judgement * proof
  | P_ExFalso        of judgement * proof

val label : proof -> formula

val env : proof -> proof_env

val judgement : proof -> judgement

val assumption : 'a env -> formula -> proof

val imp_i : formula -> proof -> proof

val imp_e : proof -> proof -> proof

val bot_e : formula -> proof -> proof

val constr_i : proof_env -> constr -> proof

val constr_e : proof_env -> proof
(** [constr_e env] returns a proof of [false] if constraints of [env] are contradictory *)

val constr_imp_i : constr -> proof -> proof

val constr_imp_e : proof -> proof -> proof

val constr_and_i : constr -> proof -> proof

val constr_and_e_left : proof -> proof

val constr_and_e_right : proof -> proof

val forall_atom_i : atom_binder -> proof -> proof

val forall_atom_e : permuted_atom -> proof -> proof

val forall_term_i : var_binder -> proof -> proof

val forall_term_e : term -> proof -> proof

val exists_atom_i : atom_binder -> permuted_atom -> formula -> proof -> proof
(** [exists_atom_i a b f p] is a proof of [exists a : atom. f] where [b] is the witness and [p] is proof of [(a |-> b) f]*)

val exists_term_i : var_binder -> term -> formula -> proof -> proof
(** [exists_term_i x t f p] is a proof of [exists x : term. f] where [t] is the witness and [p] is proof of [(x |=> t) f]*)

val exist_e : proof -> string -> proof -> proof

val and_i : proof list -> proof

val and_e : formula -> proof -> proof

val or_i : (string * formula) list -> proof -> proof

val or_e : proof -> proof list -> proof

val induction_e : var_binder -> var_binder -> proof -> proof

val equivalent : formula -> int -> proof -> proof

val subst_atom : atom -> permuted_atom -> judgement -> proof -> proof

val subst_var : var -> term -> judgement -> proof -> proof

module Axiom : sig
  val compare_atoms : proof

  val exists_fresh : proof
end
