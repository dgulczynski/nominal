open Types
open Common
open ProofCommon
open ProofEnv
open ProofException

type proof_env = formula env

type judgement = proof_env * formula

type proof =
  | P_Ax          of judgement
  | P_Intro       of judgement * proof
  | P_Apply       of judgement * proof * proof
  | P_ExFalso     of judgement * proof
  | P_ConstrIntro of judgement * proof
  | P_ConstrApply of judgement * proof * proof

let label = function
  | P_Ax (_, f)
  | P_Intro ((_, f), _)
  | P_Apply ((_, f), _, _)
  | P_ConstrIntro ((_, f), _)
  | P_ConstrApply ((_, f), _, _)
  | P_ExFalso ((_, f), _) -> f

let env = function
  | P_Ax (e, _)
  | P_Intro ((e, _), _)
  | P_Apply ((e, _), _, _)
  | P_ConstrIntro ((e, _), _)
  | P_ConstrApply ((e, _), _, _)
  | P_ExFalso ((e, _), _) -> e

let judgement proof = (env proof, label proof)

let by_assumption identifiers f = P_Ax (ProofEnv.env identifiers [] [f], f)

let remove_assumption f = remove_assumptions (equiv f)

let imp_i f p =
  let f' = label p in
  let env = env p |> remove_assumption f in
  P_Intro ((env, F_Impl (f, f')), p)

let imp_e p1 p2 =
  match (label p1, label p2) with
  | f1, f2 when f2 === premise f1 ->
      let env = union (env p1) (env p2) in
      P_Apply ((env, conclusion f1), p1, p2)
  | f1, f2 -> raise $ premise_mismatch f1 f2

let constr_i env constr =
  let constraints = constraints env @ List.filter_map to_constr_op (assumptions env) in
  if Solver.solve_with_assumptions constraints constr then
    let env = ProofEnv.env [] constraints [] in
    P_Ax (env, F_Constr constr)
  else raise $ solver_failure constraints constr

let constr_imp_i c p =
  let f = label p in
  let env = env p |> remove_constraints (( = ) c) in
  P_ConstrIntro ((env, F_ConstrImpl (c, f)), p)

let constr_imp_e c_proof c_imp_proof =
  let c = to_constr $ label c_proof in
  match label c_imp_proof with
  | F_ConstrImpl (_c, f) when _c = c ->
      let env = union (env c_proof) (env c_imp_proof) in
      P_ConstrApply ((env, f), c_proof, c_imp_proof)
  | f -> raise $ premise_mismatch (F_Constr c) f

let bot_e f p =
  match label p with
  | F_Bot -> P_ExFalso ((env p, f), p)
  | f'    -> raise $ formula_mismatch F_Bot f'
