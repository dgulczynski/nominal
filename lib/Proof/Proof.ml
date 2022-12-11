open Types
open Common
open ProofCommon
open ProofEnv
open ProofException

type proof_env = formula env

type judgement = proof_env * formula

type proof =
  | P_Ax      of judgement
  | P_Intro   of judgement * proof
  | P_Apply   of judgement * proof * proof
  | P_ExFalso of judgement * proof

let label = function
  | P_Ax (_, f) | P_Intro ((_, f), _) | P_Apply ((_, f), _, _) | P_ExFalso ((_, f), _) -> f

let env = function
  | P_Ax (e, _) | P_Intro ((e, _), _) | P_Apply ((e, _), _, _) | P_ExFalso ((e, _), _) -> e

let judgement proof = (env proof, label proof)

let by_assumption identifiers f = P_Ax (ProofEnv.env identifiers [] [f], f)

let remove_assumption f =
  remove_assumptions (equiv f)
  %
  match f with
  | F_Constr c -> remove_constraints (( = ) c)
  | _          -> id

let imp_i f p =
  let f' = label p in
  let env = env p |> remove_assumption f in
  P_Intro ((env, F_Impl (f, f')), p)

let imp_e p1 p2 =
  match (label p1, label p2) with
  | F_Impl (f2', f), f2 when f2 === f2' -> P_Apply ((union (env p1) (env p2), f), p1, p2)
  | f1, f2 -> raise $ premise_mismatch f1 f2

let bot_e f p =
  match label p with
  | F_Bot -> P_ExFalso ((env p, f), p)
  | f'    -> raise $ formula_mismatch F_Bot f'

let constr_i env constr =
  let constraints = constraints env in
  if Solver.solve_with_assumptions constraints constr then
    let env = ProofEnv.env [] constraints [] in
    P_Ax (env, F_Constr constr)
  else raise $ solver_failure constraints constr
