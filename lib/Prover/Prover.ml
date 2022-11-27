open Types
open Common
open Proof
open IncProof
open ProofContext
open ProofException
open ProverInternals

let proof env f =
  let goal = (to_goal_env env, f) in
  unfinished goal PC_Root

let intro h state =
  match goal_formula state with
  | F_Impl (f1, f2) as f ->
      let env = goal_env state in
      let goal = (env_add h f1 env, f2) in
      let context = PC_Intro (to_judgement (env, f), context state) in
      unfinished goal context
  | f                    -> raise $ not_an_implication f

let apply h state =
  let env = goal_env state in
  apply_internal (hole env h) None state

let apply_thm iproof state = apply_internal iproof None state

let apply_assm h_name state =
  let env = goal_env state in
  let h = lookup env h_name in
  apply_internal (axiom (to_env env) h) (Some h_name) state

let ex_falso state =
  let context = PC_ExFalso (to_judgement $ goal state, context state) in
  let goal = (goal_env state, F_Bot) in
  unfinished goal context

let truth state =
  match goal state with
  | env, F_Top -> find_goal_in_ctx (axiom (to_env env) F_Top) (context state)
  | _, f       -> raise $ formula_mismatch F_Top f

let qed = finish
