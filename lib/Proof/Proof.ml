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
  | P_SpecializeAtom of judgement * permuted_atom * proof
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

let forall_atom_i (A_Bind (a_name, A a) as a_bind) p =
  let env, f = judgement p in
  match env |> find_bind a_name with
  | None   -> P_Intro ((env |> remove_identifier a, F_ForallAtom (a_bind, f)), p)
  | Some f -> raise $ cannot_generalize a_name f

let forall_atom_e b p =
  let env, f = judgement p in
  let on_forall_atom (A_Bind (_, a)) f = SpecializedAtom (b, (a |-> b) f) in
  let on_forall_term _ = raise % not_a_forall_atom in
  match specialize on_forall_atom on_forall_term f with
  | SpecializedAtom (b, f) -> P_SpecializeAtom ((env, f), b, p)
  | SpecializedTerm (_, f) -> raise $ not_a_forall_atom f

let forall_term_i (V_Bind (x_name, V x) as x_bind) p =
  let env, f = judgement p in
  match env |> find_bind x_name with
  | None   -> P_Intro ((env |> remove_identifier x, F_ForallTerm (x_bind, f)), p)
  | Some f -> raise $ cannot_generalize x_name f

let forall_term_e t p =
  let env, f = judgement p in
  let on_forall_atom _ = raise % not_a_forall_term in
  let on_forall_term (V_Bind (_, x)) f = SpecializedTerm (t, (x |=> t) f) in
  match specialize on_forall_atom on_forall_term f with
  | SpecializedAtom (_, f) -> raise $ not_a_forall_term f
  | SpecializedTerm (t, f) -> P_SpecializeTerm ((env, f), t, p)

let exists_atom_i (A_Bind (_, A a) as a_bind) b f_a p =
  let f = (A a |-> b) f_a in
  let env, f' = judgement p in
  if f === f' <| env then
    let env = env |> remove_identifier a |> remove_assumption f_a in
    P_Intro ((env, F_ExistsAtom (a_bind, f_a)), p)
  else raise $ formula_mismatch f f'

let exists_term_i (V_Bind (_, V x) as x_bind) t f_x p =
  let f = (V x |=> t) f_x in
  let env, f' = judgement p in
  if f === f' <| env then
    let env = env |> remove_identifier x |> remove_assumption f_x in
    P_Intro ((env, F_ExistsTerm (x_bind, f_x)), p)
  else raise $ formula_mismatch f f'

let exist_e p_exists witness p =
  let env, f = judgement p in
  let remove_witness = function
    | F_ExistsTerm (V_Bind (_, x), f_x) -> (
      match Utils.bind_by_name witness (identifiers env) with
      | Some (Bind (_, K_Var w)) -> remove_identifier w %> remove_assumption ((x |=> var (V w)) f_x)
      | _                        -> failwith ("not a var " ^ witness) )
    | F_ExistsAtom (A_Bind (_, a), f_a) -> (
      match Utils.bind_by_name witness (identifiers env) with
      | Some (Bind (_, K_Atom w)) -> remove_identifier w %> remove_assumption ((a |-> pure (A w)) f_a)
      | _                         -> failwith ("not an atom " ^ witness) )
    | g                                 -> raise $ not_an_exists g
  in
  let env_x, f_x = judgement p_exists in
  P_Witness ((env |> union env_x |> remove_witness f_x, f), p_exists, p)

let merge_envs = List.fold_left (flip $ union % env) $ empty id

let and_i = function
  | [] | [_] -> raise $ ProofException "Cannot introduce conjunction with less than two conjuncts"
  | ps       ->
      let f = F_And (List.map (pair "" % label) ps) in
      P_AndIntro ((merge_envs ps, f), ps)

let and_e f p_fs =
  match judgement p_fs with
  | _, F_And [] | _, F_And [_] ->
      raise $ ProofException "Cannot eliminate conjunction with less than two conjuncts"
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
let induction_e (V_Bind (x_name, V x) as x_bind) (V_Bind (y_name, V y)) p =
  let f_x = label p in
  let f_y = (V x |=> var (V y)) f_x in
  let ind_hyp = F_ForallTerm (V_Bind (y_name, V y), F_ConstrImpl (var (V y) <: var (V x), f_y)) in
  let env = env p |> remove_assumption ind_hyp in
  match List.filter_map (fun v -> find_bind v env) [x_name; y_name] with
  | []     -> P_Intro ((env |> remove_identifier x, F_ForallTerm (x_bind, f_x)), p)
  | f :: _ ->
      raise
      $ cannot_generalize
          (x_name ^ "(" ^ string_of_int x ^ ")" ^ " or " ^ y_name ^ "(" ^ string_of_int y ^ ")" ^ "\n")
          f

let equivalent f n p =
  let env, fe = judgement p in
  let env, _, fn = computeWHNF env n f in
  if fe === fn <| env then P_Equivalent ((env, f), n, p) else raise $ formula_mismatch f fe

let subst_atom a b (env, f) p =
  let solver_goal = atom a =: T_Atom b in
  let subst_goal _ =
    let env = subst_atom ( |-> ) a b env in
    let f = (a |-> b) f in
    P_Substitution ((env, f), p)
  in
  solver_proof (env, F_Constr solver_goal) solver_goal subst_goal

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
    let a = fresh_atom () and b = fresh_atom () in
    let constr_same = F_Constr (atom a =: atom b) in
    let constr_diff = F_Constr (a =/=: pure b) in
    axiom
    $ F_ForallAtom
        ( A_Bind ("a", a)
        , F_ForallAtom (A_Bind ("b", b), F_Or [("same", constr_same); ("different", constr_diff)]) )

  let exists_fresh =
    let a = fresh_atom () and t = fresh_var () in
    let constr_fresh = F_Constr a #: (var t) in
    axiom $ F_ForallTerm (V_Bind ("t", t), F_ExistsAtom (A_Bind ("a", a), constr_fresh))
end
