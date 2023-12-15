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
  | P_SpecializeForm of judgement * formula * proof
  | P_Witness of judgement * proof * proof
  | P_AndIntro of judgement * proof list
  | P_AndElim of judgement * proof
  | P_OrElim of judgement * proof list
  | P_Equivalent of judgement * int * proof
  | P_ExFalso of judgement * proof

val label : proof -> formula

val env : proof -> proof_env

val judgement : proof -> judgement

(* ----------- *)
(*  Γ; f |- f  *)
val assumption : 'a env -> formula -> proof

(*   Γ; Θ, f1 |- f2   *)
(* ------------------ *)
(*  Γ; Θ |- f1 => f2  *)
val imp_i : formula -> proof -> proof

(*  Γ1; Θ1 |- f1    Γ2; Θ2 |- f1 => f2  *)
(* ------------------------------------ *)
(*        Γ1 ∪ Γ2; Θ1 ∪ Θ2 |- f2        *)
val imp_e : proof -> proof -> proof

(*  Γ; Θ |- ⊥  *)
(* ----------- *)
(*  Γ; Θ |- f  *)
val bot_e : formula -> proof -> proof

(*   Γ |= c    *)
(* ----------- *)
(*  Γ; Θ |- c  *)
val constr_i : proof_env -> constr -> proof

(*   Γ |= ⊥    *)
(* ----------- *)
(*  Γ; Θ |- ⊥  *)
val constr_e : proof_env -> proof
(** [constr_e env] returns a proof of [false] if constraints of [env] are contradictory *)

(*    Γ, c; Θ |- f    *)
(* ------------------ *)
(*  Γ; Θ |- [c] => f  *)
val constr_imp_i : constr -> proof -> proof

(*  Γ1; Θ1 |- [c] => f    Γ2; Θ2 |- c  *)
(* ----------------------------------- *)
(*         Γ1 ∪ Γ2; Θ1 ∪ Θ2 |- f       *)
val constr_imp_e : proof -> proof -> proof

(*  Γ |= c    Γ, c; Θ |- f  *)
(* ------------------------ *)
(*     Γ; Θ |- [c] /\ f     *)
val constr_and_i : proof -> proof -> proof

(*  Γ; Θ |- [c] /\ f  *)
(* ------------------ *)
(*      Γ; Θ |- c     *)
val constr_and_e_left : proof -> proof

(*  Γ; Θ |- [c] /\ f    Γ; Θ |- f : Prop *)
(* ------------------------------------- *)
(*               Γ; Θ |- f               *)
val constr_and_e_right : proof -> proof

(*  a ∉ FV(Γ; Θ)    Γ; Θ |- f  *)
(* --------------------------- *)
(*    Γ; Θ |- ∀ a :atom. f     *)
val forall_atom_i : atom_binder -> proof -> proof

(*  Γ; Θ |- ∀ a :atom. f  *)
(* ---------------------- *)
(*    Γ; Θ |- f{a -> b}   *)
val forall_atom_e : permuted_atom -> proof -> proof

(*  x ∉ FV(Γ; Θ)    Γ; Θ |- f  *)
(* --------------------------- *)
(*    Γ; Θ |- ∀ x :term. f    *)
val forall_term_i : var_binder -> proof -> proof

(*  Γ; Θ |- ∀ x :term. f  *)
(* ---------------------- *)
(*    Γ; Θ |- f{x -> e}   *)
val forall_term_e : term -> proof -> proof

(*  p ∉ FV(Γ; Θ)    Γ; Θ |- f  *)
(* --------------------------- *)
(*       Γ; Θ |- ∀ p:k. f      *)
val forall_form_i : fvar_binder -> proof -> proof

(*  Γ; Θ |- ∀ p :k. f    Γ; Θ |- g : k  *)
(* ------------------------------------ *)
(*            Γ; Θ |- f{p -> g}         *)
val forall_form_e : formula -> proof -> proof

(*    Γ; Θ |- f{a -> b}   *)
(* ---------------------- *)
(*  Γ; Θ |- ∃ a :atom. f  *)
val exists_atom_i : atom_binder -> permuted_atom -> formula -> proof -> proof
(** [exists_atom_i a b f p] is a proof of [exists a :atom. f] where [b] is the witness and [p] is proof of [(a |-> b) f]*)

(*    Γ; Θ |- f{x -> e}   *)
(* ---------------------- *)
(*  Γ; Θ |- ∃ x :term. f  *)
val exists_term_i : var_binder -> term -> formula -> proof -> proof
(** [exists_term_i x t f p] is a proof of [exists x :term. f] where [t] is the witness and [p] is proof of [(x |=> t) f]*)

(*  Γ; Θ |- f{x -> g}    Γ; Θ |- g : k  *)
(* ------------------------------------ *)
(*           Γ; Θ |- ∃ x :k. f          *)
val exists_form_i : fvar_binder -> formula -> formula -> proof -> proof
(** [exists_term_i x g f p] is a proof of [exists x :k. f] where [g] is the witness and [p] is proof of [(x |==> g) f]*)

(*  Γ_1; Θ_1 |- ∃ a :atom. f  *)
(*  Γ_2; Θ_2, f{a -> b} |- g  *)
(*  b ∉ FV(Γ1 ∪ Γ2; Θ1 ∪ Θ2)  *)
(* -------------------------- *)
(*   Γ1 ∪ Γ2; Θ1 ∪ Θ2 |- g    *)

(*  Γ_1; Θ_1 |- ∃ x :term. f  *)
(*  Γ_2; Θ_2, f{x -> y} |- g  *)
(*  y ∉ FV(Γ1 ∪ Γ2; Θ1 ∪ Θ2)  *)
(* -------------------------- *)
(*   Γ1 ∪ Γ2; Θ1 ∪ Θ2 |- g    *)

(*  Γ_1; Θ_1 |- ∃ x :k. f      *)
(*  Γ_2; Θ_2, f{x -> y} |- g   *)
(*  y ∉ FV(Γ1 ∪ Γ2; Θ1 ∪ Θ2)   *)
(* Γ1 ∪ Γ2; Θ1 ∪ Θ2 |- k <: k' *)
(* --------------------------- *)
(*    Γ1 ∪ Γ2; Θ1 ∪ Θ2 |- g    *)
val exist_e : proof -> string -> proof -> proof

(*          Γ1; Θ1 |- f1  ...  Γn; Θn |- fn          *)
(* ------------------------------------------------- *)
(*  Γ1 ∪ ... ∪ Γn; Θ1 ∪ ... ∪ Θn |- f1 /\ ... /\ fn  *)
val and_i : proof list -> proof

(*  Γ; Θ |- f1 /\ ... /\ fn    i ∈ [1..n]  *)
(* --------------------------------------- *)
(*                Γ; Θ |- fi               *)
val and_e : formula -> proof -> proof

(*  Γ; Θ |- fi   i ∈ [1..n]  *)
(* ------------------------- *)
(*  Γ; Θ |- f1 \/ ... \/ fn  *)
val or_i : (string * formula) list -> proof -> proof

(*  Γ; Θ |- f1 \/ .. \/ fn    ∀(i ∈ [1..n]). Γ; Θ, fi |- g  *)
(* -------------------------------------------------------- *)
(*                        Γ; Θ |- g                         *)
val or_e : proof -> proof list -> proof

(*  Γ; Θ, (∀ y :term. [y < x] => f(y)) |- f(x)  *)
(* -------------------------------------------- *)
(*            Γ; Θ |- ∀ x :term. f(x)           *)
val induction_e : var_binder -> var_binder -> proof -> proof

(*  Γ; Θ |- g    Γ; Θ |- f === g  *)
(* ------------------------------ *)
(*            Γ; Θ |- f           *)
val equivalent : judgement -> int -> proof -> proof

(*        Γ |= a = b    Γ; Θ |- f      *)
(* ----------------------------------- *)
(*  Γ{a -> b}; Θ{x -> t} |- f{a -> b}  *)
val subst_atom : atom -> permuted_atom -> judgement -> proof -> proof

(*       Γ |= x = t    Γ; Θ |- f       *)
(* ----------------------------------- *)
(*  Γ{x -> t}; Θ{x -> t} |- f{x -> t}  *)
val subst_var : var -> term -> judgement -> proof -> proof

val truth_i : proof

module Axiom : sig
  (* --------------------------------------- *)
  (*  |- ∀ a b :atom. (a = b) \/ (a =/= b)  *)
  val compare_atoms : proof

  (* ---------------------------------- *)
  (*  |- ∀ t :term. ∃ a :atom. (a # t)  *)
  val exists_fresh : proof

  (* ------------------------------------------------- *)
  (*  |- ∀ t :term. (∃ a :atom. t = a)                 *)
  (*             \/ (∃ a :atom. ∃ t' :term. t = a.t')  *)
  (*             \/ (∃ t1 t2 :term. t = t1 t2)         *)
  (*             \/ (symbol t)                         *)
  val term_inversion : proof
end
