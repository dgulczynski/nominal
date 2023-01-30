open Types
open Common
open ProofCommon
open ProofEnv
open ProofException
open Substitution

type proof_env = formula env

type judgement = proof_env * formula

type proof =
  | P_Ax             of judgement
  | P_Intro          of judgement * proof
  | P_Apply          of judgement * proof * proof
  | P_ConstrIntro    of judgement * proof
  | P_ConstrApply    of judgement * proof * proof
  | P_SpecializeAtom of judgement * atom * proof
  | P_SpecializeTerm of judgement * term * proof
  | P_Witness        of judgement * proof * proof
  | P_ExFalso        of judgement * proof

let label = function
  | P_Ax (_, f)
  | P_Intro ((_, f), _)
  | P_Apply ((_, f), _, _)
  | P_ConstrIntro ((_, f), _)
  | P_ConstrApply ((_, f), _, _)
  | P_SpecializeAtom ((_, f), _, _)
  | P_SpecializeTerm ((_, f), _, _)
  | P_Witness ((_, f), _, _)
  | P_ExFalso ((_, f), _) -> f

let env = function
  | P_Ax (e, _)
  | P_Intro ((e, _), _)
  | P_Apply ((e, _), _, _)
  | P_ConstrIntro ((e, _), _)
  | P_ConstrApply ((e, _), _, _)
  | P_SpecializeAtom ((e, _), _, _)
  | P_SpecializeTerm ((e, _), _, _)
  | P_Witness ((e, _), _, _)
  | P_ExFalso ((e, _), _) -> e

let judgement proof = (env proof, label proof)

let axiom identifiers f = P_Ax (ProofEnv.env identifiers [] [f], f)

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
  let identifiers = identifiers env in
  let assumptions = List.filter (Option.is_some % to_constr_op) $ assumptions env in
  let constraints = constraints env in
  let solver_assumptions = List.filter_map to_constr_op assumptions @ constraints in
  if Solver.solve_with_assumptions solver_assumptions constr then
    let env = ProofEnv.env identifiers constraints assumptions in
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
  match judgement p with
  | env, F_Bot -> P_ExFalso ((env, f), p)
  | _, f'      -> raise $ formula_mismatch F_Bot f'

let forall_atom_i (A a_name as a) p =
  let env, f = judgement p in
  match env |> find_bind id a_name with
  | None   -> P_Intro ((env |> remove_identifier a_name, F_ForallAtom (a, f)), p)
  | Some f -> raise $ cannot_generalize a_name f

let forall_atom_e (A _b_name as b) p =
  match judgement p with
  | env, F_ForallAtom (a, f) -> P_SpecializeAtom ((env, (a |-> b) f), b, p)
  | _, f                     -> raise $ not_a_forall f

let forall_term_i (V x_name as x) p =
  let env, f = judgement p in
  match env |> find_bind id x_name with
  | None   -> P_Intro ((env |> remove_identifier x_name, F_ForallTerm (x, f)), p)
  | Some f -> raise $ cannot_generalize x_name f

let forall_term_e t p =
  match judgement p with
  | env, F_ForallTerm (x, f) -> P_SpecializeTerm ((env, (x |=> t) f), t, p)
  | _, f                     -> raise $ not_a_forall f

let exists_atom_i (A a_name as a) b f_a p =
  let f = (a |-> b) f_a in
  let f' = label p in
  if f === f' then
    let env = env p |> remove_identifier a_name |> remove_assumption f_a in
    P_Intro ((env, F_ExistsAtom (a, f_a)), p)
  else raise $ formula_mismatch f f'

let exists_term_i (V x_name as x) t f_x p =
  let f = (x |=> t) f_x in
  let f' = label p in
  if f === f' then
    let env = env p |> remove_identifier x_name |> remove_assumption f_x in
    P_Intro ((env, F_ExistsTerm (x, f_x)), p)
  else raise $ formula_mismatch f f'

let exist_e p_exists p =
  let env, f = judgement p in
  match judgement p_exists with
  | env_x, F_ExistsAtom (A x, f_x) | env_x, F_ExistsTerm (V x, f_x) ->
      let env = env |> union env_x |> remove_identifier x |> remove_assumption f_x in
      P_Witness ((env, f), p_exists, p)
  | _, g -> raise $ not_an_exists g
