open Common
open Proof
open ProofException
open ProverGoal
open Types

(** Possibly incomplete proof with the same structure as [proof], but with _holes_ *)
type incproof =
  | PI_Hole    of goal
  | PI_Axiom   of judgement
  | PI_Intro   of judgement * incproof
  | PI_Apply   of judgement * incproof * incproof
  | PI_ExFalso of judgement * incproof

let label' = function
  | PI_Hole (_, f)
  | PI_Axiom (_, f)
  | PI_Intro ((_, f), _)
  | PI_Apply ((_, f), _, _)
  | PI_ExFalso ((_, f), _) -> f

let env' = function
  | PI_Hole (e, _) -> to_env e
  | PI_Axiom (e, _) | PI_Intro ((e, _), _) | PI_Apply ((e, _), _, _) | PI_ExFalso ((e, _), _) -> e

let judgement' incproof = (env' incproof, label' incproof)

let rec hasHoles = function
  | PI_Hole _          -> true
  | PI_Axiom _         -> false
  | PI_Intro (_, p)    -> hasHoles p
  | PI_ExFalso (_, p)  -> hasHoles p
  | PI_Apply (_, l, r) -> hasHoles l || hasHoles r

let rec incproof_to_proof = function
  | PI_Axiom (_, f) -> by_assumption f
  | PI_Apply (_, lproof, rproof) -> imp_e (incproof_to_proof rproof) (incproof_to_proof lproof)
  | PI_ExFalso ((_, f), incproof) -> bot_e f $ incproof_to_proof incproof
  | PI_Intro ((_, F_Impl (f, _)), incproof) -> imp_i f $ incproof_to_proof incproof
  | PI_Intro ((_, f), _) -> raise $ not_an_implication f
  | PI_Hole _ -> raise hole_in_proof

let hole env f = PI_Hole (env, f)

let axiom env f = PI_Axiom (env, f)
