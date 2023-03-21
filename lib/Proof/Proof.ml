open Types
open Common
open ProofCommon
open ProofEnv
open ProofEquiv
open Permutation
open ProofException
open Substitution

type proof_env = formula env

type judgement = proof_env * formula

type proof =
  | P_Ax             of judgement
  | P_Intro          of judgement * proof
  | P_Apply          of judgement * proof * proof
  | P_ConstrApply    of judgement * proof * proof
  | P_ConstrAndElim  of judgement * proof
  | P_SpecializeAtom of judgement * atom * proof
  | P_SpecializeTerm of judgement * term * proof
  | P_Witness        of judgement * proof * proof
  | P_AndIntro       of judgement * proof list
  | P_AndElim        of judgement * proof
  | P_OrElim         of judgement * proof list
  | P_Equivalent     of judgement * int * proof
  | P_Substitution   of judgement * proof
  | P_ExFalso        of judgement * proof

let label = function
  | P_Ax (_, f)
  | P_Intro ((_, f), _)
  | P_Apply ((_, f), _, _)
  | P_ConstrApply ((_, f), _, _)
  | P_ConstrAndElim ((_, f), _)
  | P_SpecializeAtom ((_, f), _, _)
  | P_SpecializeTerm ((_, f), _, _)
  | P_Witness ((_, f), _, _)
  | P_AndIntro ((_, f), _)
  | P_AndElim ((_, f), _)
  | P_OrElim ((_, f), _)
  | P_Equivalent ((_, f), _, _)
  | P_Substitution ((_, f), _)
  | P_ExFalso ((_, f), _) -> f

let env = function
  | P_Ax (e, _)
  | P_Intro ((e, _), _)
  | P_Apply ((e, _), _, _)
  | P_ConstrApply ((e, _), _, _)
  | P_ConstrAndElim ((e, _), _)
  | P_SpecializeAtom ((e, _), _, _)
  | P_SpecializeTerm ((e, _), _, _)
  | P_Witness ((e, _), _, _)
  | P_AndIntro ((e, _), _)
  | P_AndElim ((e, _), _)
  | P_OrElim ((e, _), _)
  | P_Equivalent ((e, _), _, _)
  | P_Substitution ((e, _), _)
  | P_ExFalso ((e, _), _) -> e

let judgement proof = (env proof, label proof)

let assumption env f = P_Ax (ProofEnv.env (identifiers env) (constraints env) [f] (mapping env) id, f)

let remove_assumptions_equiv_to to_formula f env = remove_assumptions (fun g -> f === to_formula g <| env) env

let remove_assumption = remove_assumptions_equiv_to id

let imp_i f p =
  let f' = label p in
  let env = env p |> remove_assumption f in
  P_Intro ((env, F_Impl (f, f')), p)

let imp_e p1 p2 =
  let env = union (env p1) (env p2) in
  match (label p1, label p2) with
  | f1, f2 when f2 === premise f1 <| env -> P_Apply ((env, conclusion f1), p1, p2)
  | f1, f2 -> raise $ premise_mismatch f1 f2

let solver_proof (env, f) solver_goal on_solved =
  let constr_assumptions = List.filter_map to_constr_op $ assumptions env in
  let assumptions = List.map (fun c -> F_Constr c) constr_assumptions in
  let env = ProofEnv.env (identifiers env) (constraints env) assumptions (mapping env) id in
  let solver_assumptions = constr_assumptions @ constraints env in
  match Solver.solve_with_assumptions solver_assumptions solver_goal with
  | true  -> on_solved (env, f)
  | false -> raise $ solver_failure solver_assumptions f

let constr_i env constr =
  let judgement = (env, F_Constr constr) in
  solver_proof judgement constr $ fun jgmt -> P_Ax jgmt

let constr_e env =
  let judgement = (env, F_Bot) in
  solver_proof judgement Solver.absurd % const $ P_Ax judgement

let constr_imp_i c p =
  let f = label p in
  let env = env p |> remove_constraints (( = ) c) in
  P_Intro ((env, F_ConstrImpl (c, f)), p)

let constr_imp_e c_proof c_imp_proof =
  let c = to_constr $ label c_proof in
  match label c_imp_proof with
  | F_ConstrImpl (_c, f) when _c = c ->
      let env = union (env c_proof) (env c_imp_proof) in
      P_ConstrApply ((env, f), c_proof, c_imp_proof)
  | f -> raise $ premise_mismatch (F_Constr c) f

let constr_and_i c p =
  let f = label p in
  let env = env p |> remove_constraints (( = ) c) in
  P_Intro ((env, F_ConstrAnd (c, f)), p)

let constr_and_e_left c_and_proof =
  match judgement c_and_proof with
  | env, F_ConstrAnd (_, f) -> P_ConstrAndElim ((env, f), c_and_proof)
  | _, f                    -> raise $ not_a_constr_and f

let constr_and_e_right c_and_proof =
  match judgement c_and_proof with
  | env, F_ConstrAnd (c, _) -> P_ConstrAndElim ((env, F_Constr c), c_and_proof)
  | _, f                    -> raise $ not_a_constr_and f

let bot_e f p =
  match judgement p with
  | env, F_Bot -> P_ExFalso ((env, f), p)
  | _, f'      -> raise $ formula_mismatch F_Bot f'

let forall_atom_i (A a_name as a) p =
  let env, f = judgement p in
  match env |> find_bind a_name with
  | None   -> P_Intro ((env |> remove_identifier a_name, F_ForallAtom (a, f)), p)
  | Some f -> raise $ cannot_generalize a_name f

let forall_atom_e (A _b_name as b) p =
  let env, f = judgement p in
  let on_forall_atom a f = SpecializedAtom (b, (a |-> b) f) in
  let on_forall_term _ = raise % not_a_forall_atom in
  match specialize on_forall_atom on_forall_term f with
  | SpecializedAtom (b, f) -> P_SpecializeAtom ((env, f), b, p)
  | SpecializedTerm (_, f) -> raise $ not_a_forall_atom f

let forall_term_i (V x_name as x) p =
  let env, f = judgement p in
  match env |> find_bind x_name with
  | None   -> P_Intro ((env |> remove_identifier x_name, F_ForallTerm (x, f)), p)
  | Some f -> raise $ cannot_generalize x_name f

let forall_term_e t p =
  let env, f = judgement p in
  let on_forall_atom _ = raise % not_a_forall_term in
  let on_forall_term x f = SpecializedTerm (t, (x |=> t) f) in
  match specialize on_forall_atom on_forall_term f with
  | SpecializedAtom (_, f) -> raise $ not_a_forall_term f
  | SpecializedTerm (t, f) -> P_SpecializeTerm ((env, f), t, p)

let exists_atom_i (A a_name as a) b f_a p =
  let f = (a |-> b) f_a in
  let env, f' = judgement p in
  if f === f' <| env then
    let env = env |> remove_identifier a_name |> remove_assumption f_a in
    P_Intro ((env, F_ExistsAtom (a, f_a)), p)
  else raise $ formula_mismatch f f'

let exists_term_i (V x_name as x) t f_x p =
  let f = (x |=> t) f_x in
  let env, f' = judgement p in
  if f === f' <| env then
    let env = env |> remove_identifier x_name |> remove_assumption f_x in
    P_Intro ((env, F_ExistsTerm (x, f_x)), p)
  else raise $ formula_mismatch f f'

let exist_e p_exists witness p =
  let remove_witness = function
    | F_ExistsTerm (V x, f_x) -> remove_identifier witness %> remove_assumption ((V x |=> var (V witness)) f_x)
    | F_ExistsAtom (A a, f_a) -> remove_identifier witness %> remove_assumption ((A a |-> A witness) f_a)
    | g                       -> raise $ not_an_exists g
  in
  let env, f = judgement p in
  let env_x, f_x = judgement p_exists in
  P_Witness ((env |> remove_witness f_x |> union env_x, f), p_exists, p)

let merge_envs = List.fold_left (flip $ union % env) $ empty id

let and_i = function
  | [] | [_] -> raise $ ProofException "Cannot introduce conjunction with less than two conjuncts"
  | ps       ->
      let f = F_And (List.map (pair "" % label) ps) in
      P_AndIntro ((merge_envs ps, f), ps)

let and_e f p_fs =
  match judgement p_fs with
  | _, F_And [] | _, F_And [_] -> raise $ ProofException "Cannot eliminate conjunction with less than two conjuncts"
  | env, F_And fs when List.exists (fun (_, g) -> f === g <| env) fs -> P_AndElim ((env, f), p_fs)
  | _, g -> raise $ not_a_conjunction_with f g

let or_i disjuncts p =
  match disjuncts with
  | [] | [_] -> raise $ ProofException "Cannot introduce disjunction with less than two disjuncts"
  | fs       -> (
    match judgement p with
    | env, f when List.exists (fun (_, g) -> f === g <| env) fs -> P_Intro ((env, F_Or fs), p)
    | _, f -> raise % not_a_disjunction_with f $ F_Or fs )

let or_e or_proof ps =
  match ps with
  | [] | [_] -> raise $ ProofException "Cannot eliminate disjunction with less than two disjuncts"
  | p :: _   ->
      let _, _, disjunction = uncurry (flip computeWHNF 10) $ judgement or_proof in
      let c = conclusion $ label p in
      let fs = disjuncts disjunction in
      let test_proof f p =
        let env, f' = judgement p in
        f' === F_Impl (f, c) <| env
      in
      if List.for_all2 (test_proof % snd) fs ps then P_OrElim ((merge_envs (or_proof :: ps), c), ps)
      else
        let f = F_Or (List.map (pair "" % premise % label) ps) in
        raise $ formula_mismatch (label or_proof) f

(*   G, x, forall y:term. [y < x] => f(y) |- f(x)  *)
(* ----------------------------------------------- *)
(*          G |-  forall x : term. f(x)            *)
let induction_e (V x_name as x) (V y_name as y) p =
  let f_x = label p in
  let f_y = (x |=> var y) f_x in
  let ind_hyp = F_ForallTerm (y, F_ConstrImpl (var y <: var x, f_y)) in
  let env = env p |> remove_assumption ind_hyp in
  match List.filter_map (fun v -> find_bind v env) [x_name; y_name] with
  | []     -> P_Intro ((env |> remove_identifier x_name, F_ForallTerm (x, f_x)), p)
  | f :: _ -> raise $ cannot_generalize (x_name ^ " or " ^ y_name) f

let equivalent f n p =
  let env, fe = judgement p in
  let env, _, fn = computeWHNF env n f in
  if fe === fn <| env then P_Equivalent ((env, f), n, p) else raise $ formula_mismatch f fe

let rename (V x_name as x) (V y_name as y) p =
  let env, f = judgement p in
  match env |> find_bind y_name with
  | Some f ->
      failwith
      $ Printing.unwords
          [ "cannot rename"
          ; x_name
          ; "to"
          ; y_name
          ; "its bound in"
          ; Printing.string_of_formula_in_env (all_identifiers env) f ]
  | None   -> P_Substitution ((subst_var ( |=> ) x (var y) env, (x |=> var y) f), p)

let subst_var x t (env, f) p =
  let solver_goal = var x =: t in
  let subst_goal _ =
    let env = subst_var ( |=> ) x t env in
    let f = (x |=> t) f in
    (* TODO: add checks if [env p] is the same as [env]? *)
    P_Substitution ((env, f), p)
  in
  solver_proof (env, F_Constr solver_goal) solver_goal subst_goal

module Axiom = struct
  let axiom f = P_Ax (empty id, f)

  let compare_atoms =
    let a = A "a" and b = A "b" in
    let constr_same = F_Constr (atom a =: atom b) in
    let constr_diff = F_Constr (a =/=: pure b) in
    axiom $ F_ForallAtom (a, F_ForallAtom (b, F_Or [("same", constr_same); ("different", constr_diff)]))

  let exists_fresh =
    let a = A "a" and t = V "t" in
    let constr_fresh = F_Constr a #: (var t) in
    axiom $ F_ForallTerm (t, F_ExistsAtom (a, constr_fresh))
end