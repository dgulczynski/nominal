open Types
open Proof
open Common
open ProofException

(** Possibly incomplete proof with the same structure as [proof], but with _holes_ *)
type incproof =
  | PI_Hole    of goal
  | PI_Axiom   of judgement
  | PI_Intro   of judgement * incproof
  | PI_Apply   of judgement * incproof * incproof
  | PI_ExFalso of judgement * incproof

and goal_env = (string * formula) list

and goal = goal_env * formula

let to_goal_env env = List.mapi (fun i h -> (Printf.sprintf "H%d" i, h)) env

let to_env env = List.map snd env

let to_judgement (env, f) = (to_env env, f)

let to_goal (env, f) = (to_goal_env env, f)

let label' = function
  | PI_Hole (_, f)
  | PI_Axiom (_, f)
  | PI_Intro ((_, f), _)
  | PI_Apply ((_, f), _, _)
  | PI_ExFalso ((_, f), _) -> f

let env' = function
  | PI_Hole (e, _) -> to_env e
  | PI_Axiom (e, _) | PI_Intro ((e, _), _) | PI_Apply ((e, _), _, _) | PI_ExFalso ((e, _), _) -> e

let judgement' iproof = (env' iproof, label' iproof)

let rec hasHoles = function
  | PI_Hole _          -> true
  | PI_Axiom _         -> false
  | PI_Intro (_, p)    -> hasHoles p
  | PI_ExFalso (_, p)  -> hasHoles p
  | PI_Apply (_, l, r) -> hasHoles l || hasHoles r

let rec iproof_to_proof = function
  | PI_Axiom (_, f) -> by_assumption f
  | PI_Apply (_, lproof, rproof) -> imp_e (iproof_to_proof rproof) (iproof_to_proof lproof)
  | PI_ExFalso ((_, f), iproof) -> bot_e f $ iproof_to_proof iproof
  | PI_Intro ((_, F_Impl (f, _)), iproof) -> imp_i f $ iproof_to_proof iproof
  | PI_Intro ((_, f), _) -> raise $ not_an_implication f
  | PI_Hole _ -> raise hole_in_proof

let hole env f = PI_Hole (env, f)

let axiom env f = PI_Axiom (env, f)