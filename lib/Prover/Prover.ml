open Types
open Common
open IncProof
open ProofException
open ProofEnv
open ProverGoal
open ProverInternals

let proof env f =
  let goal = (env, f) in
  unfinished goal PC_Root

let intro h state =
  match goal_formula state with
  | F_Impl (f1, f2) as f ->
      let env = goal_env state |> add_assumption (h, f1) in
      let context = PC_Intro (to_judgement (env, f), context state) in
      unfinished (env, f2) context
  | f                    -> raise $ not_an_implication f

let apply h state =
  let env = goal_env state in
  apply_internal (proof_hole env h) state

let apply_thm proof state = apply_internal (proven proof) state

let apply_assm h_name state =
  let env = goal_env state in
  let h = lookup env h_name in
  apply_internal ~h_name (proof_axiom h) state

let ex_falso state =
  let context = PC_ExFalso (to_judgement $ goal state, context state) in
  let goal = (goal_env state, F_Bot) in
  unfinished goal context

let truth state =
  match goal_formula state with
  | F_Top -> find_goal_in_ctx (proof_axiom F_Top) (context state)
  | f     -> raise $ formula_mismatch F_Top f

let qed = finish
