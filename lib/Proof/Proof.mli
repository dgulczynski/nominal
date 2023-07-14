open Types
open ProofEnv

type proof_env = formula env

type judgement = proof_env * formula

type proof = private
  | P_Ax of judgement
  | P_Intro of judgement * proof
  | P_Apply of judgement * proof * proof
  | P_ConstrApply of judgement * proof * proof
  | P_ConstrAndElim of judgement * proof
  | P_SpecializeAtom of judgement * permuted_atom * proof
  | P_SpecializeTerm of judgement * term * proof
  | P_Witness of judgement * proof * proof
  | P_AndIntro of judgement * proof list
  | P_AndElim of judgement * proof
  | P_OrElim of judgement * proof list
  | P_Equivalent of judgement * int * proof
  | P_ExFalso of judgement * proof

val label : proof -> formula

val env : proof -> proof_env

val judgement : proof -> judgement

(*   f ∈ Γ   *)
(* --------- *)
(*   Γ |- f  *)
val assumption : 'a env -> formula -> proof

(*   Γ, f1 |- f2    *)
(* ---------------- *)
(*  Γ |- f1 => f2   *)
val imp_i : formula -> proof -> proof

(*  Γ1 |- f1 => f2   Γ2 |- f2  *)
(* --------------------------- *)
(*        Γ1 ∪ Γ2 |- f2        *)
val imp_e : proof -> proof -> proof

(*  Γ |- ⊥  *)
(* -------- *)
(*  Γ |- f  *)
val bot_e : formula -> proof -> proof

(*  Γ |= c  *)
(* -------- *)
(*  Γ |- c  *)
val constr_i : proof_env -> constr -> proof

(*  Γ |= ⊥  *)
(* -------- *)
(*  Γ |- ⊥  *)
val constr_e : proof_env -> proof
(** [constr_e env] returns a proof of [false] if constraints of [env] are contradictory *)

(*    Γ, c |- f    *)
(* --------------- *)
(*  Γ |- [c] => f  *)
val constr_imp_i : constr -> proof -> proof

(*  Γ1 |- [c] => f   Γ2 |- c  *)
(* -------------------------- *)
(*         Γ1 ∪ Γ2 |- f       *)
val constr_imp_e : proof -> proof -> proof

(*    Γ, c |- f    *)
(* --------------- *)
(*  Γ |- [c] /\ f  *)
val constr_and_i : constr -> proof -> proof

(*  Γ |- [c] /\ f  *)
(* --------------- *)
(*      Γ |- c     *)
(* ??????????????? *)
val constr_and_e_left : proof -> proof

(*  Γ |- [c] /\ f  *)
(* --------------- *)
(*      Γ |- f     *)
(* ??????????????? *)
val constr_and_e_right : proof -> proof

(*  a ∉ FV(Γ)   Γ |- f  *)
(* -------------------- *)
(*  Γ |- ∀ a : atom. f  *)
val forall_atom_i : atom_binder -> proof -> proof

(*  Γ |- ∀ a : atom. f  *)
(* -------------------- *)
(*    Γ |- f{a -> b}    *)
val forall_atom_e : permuted_atom -> proof -> proof

(*  x ∉ FV(Γ)   Γ |- f  *)
(* -------------------- *)
(*  Γ |- ∀ x : term. f  *)
val forall_term_i : var_binder -> proof -> proof

(*  Γ |- ∀ x : term. f  *)
(* -------------------- *)
(*    Γ |- f{x -> e}    *)
val forall_term_e : term -> proof -> proof

(*    Γ |- f{a -> b}    *)
(* -------------------- *)
(*  Γ |- ∃ a : atom. f  *)
val exists_atom_i : atom_binder -> permuted_atom -> formula -> proof -> proof
(** [exists_atom_i a b f p] is a proof of [exists a : atom. f] where [b] is the witness and [p] is proof of [(a |-> b) f]*)

(*    Γ |- f{x -> e}    *)
(* -------------------- *)
(*  Γ |- ∃ x : term. f  *)
val exists_term_i : var_binder -> term -> formula -> proof -> proof
(** [exists_term_i x t f p] is a proof of [exists x : term. f] where [t] is the witness and [p] is proof of [(x |=> t) f]*)

(*  fresh_var(y)   Γ |- ∃ x : term. f  *)
(*          Γ, f{x -> y} |- g          *)
(* ----------------------------------- *)
(*                 Γ |- g              *)

(*  fresh_atom(b)   Γ |- ∃ a : term. f  *)
(*          Γ, f{a -> b} |- g           *)
(* ------------------------------------ *)
(*                Γ |- g                *)
val exist_e : proof -> string -> proof -> proof

(*       Γ1 |- f1 ...  Γn |- fn      *)
(* --------------------------------- *)
(*  Γ1 ∪ ... ∪ Γn |- f1 /\ .. /\ fn  *)
val and_i : proof list -> proof

(*  Γ |- f1 /\ ... /\ fn   i ∈ [1..n]  *)
(* ----------------------------------- *)
(*                Γ |- fi              *)
val and_e : formula -> proof -> proof

(*  Γ |- fi   i ∈ [1..n]  *)
(* ---------------------- *)
(*  Γ |- f1 \/ ... \/ fn  *)
val or_i : (string * formula) list -> proof -> proof

(*  Γ |- f1 \/ .. \/ fn   ∀(i ∈ [1..n]).(Γ, fi |- g)  *)
(* -------------------------------------------------- *)
(*                       Γ |- g                       *)
val or_e : proof -> proof list -> proof

(*  Γ, x, (forall y:term. [y < x] => f(y)) |- f(x)  *)
(* ------------------------------------------------ *)
(*          G |-  forall x : term. f(x)             *)
val induction_e : var_binder -> var_binder -> proof -> proof

(*  Γ |- g   Γ |- f === g  *)
(* ----------------------- *)
(*       Γ |- f            *)
val equivalent : judgement -> int -> proof -> proof

(*   Γ |= a = b   Γ |- f    *)
(* ------------------------ *)
(*  Γ{a -> b}  |- f{a -> b} *)
val subst_atom : atom -> permuted_atom -> judgement -> proof -> proof

(*   Γ |= x = t   Γ |- f    *)
(* ------------------------ *)
(*  Γ{x -> t}  |- f{x -> t} *)
val subst_var : var -> term -> judgement -> proof -> proof

module Axiom : sig
  val compare_atoms : proof

  val exists_fresh : proof

  val term_inversion : proof
end
