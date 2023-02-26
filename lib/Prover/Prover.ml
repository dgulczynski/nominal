open Types
open Common
open IncProof
open Parser
open ProofCommon
open ProofEnv
open ProofException
open ProverGoal
open ProverInternals
open Substitution

let check_props env formulas =
  let check_prop f =
    match kind_infer env f with
    | Some K_Prop -> ()
    | k           -> raise $ formula_kind_mismatch f k K_Prop
  in
  List.iter check_prop formulas

let check_input env goal =
  let assumptions = List.map snd $ assumptions env in
  check_props env $ goal :: assumptions

let proof env f =
  let _ = check_input env f in
  let goal = (env, f) in
  unfinished goal PC_Root

let intro state =
  let env, f = goal state in
  let context = PC_Intro (to_judgement (env, f), context state) in
  match f with
  | F_ConstrImpl (constr, f2) -> unfinished (env |> add_constr constr, f2) context
  | F_ForallAtom (A a, f')    -> unfinished (env |> add_atom a, f') context
  | F_ForallTerm (V x, f')    -> unfinished (env |> add_var x, f') context
  | _                         -> raise $ not_a_constr_implication f

let intros = flip (List.fold_left (flip intro_named))

let apply h state =
  let env = goal_env state in
  let _ = check_props env [h] in
  apply_internal (proof_hole env h) state

let apply_thm proof state = apply_internal (proven proof) state

let assm_proof h_name env = proof_axiom env (lookup env h_name)

let apply_assm h_name state =
  let env = goal_env state in
  apply_internal ~h_name (assm_proof h_name env) state

let apply_assm_specialized h_name specs state =
  let specialize_proof proof spec =
    match judgement' proof with
    | env, F_ForallAtom (b, f) ->
        let a = parse_atom_in_env (identifiers env) spec in
        proof_specialize_atom (env, (b |-> a) f) a proof
    | env, F_ForallTerm (x, f) ->
        let t = parse_term_in_env (identifiers env) spec in
        proof_specialize_term (env, (x |=> t) f) t proof
    | _, f                     -> raise $ not_a_forall f
  in
  let env = goal_env state in
  let h_proof = List.fold_left specialize_proof (assm_proof h_name env) specs in
  apply_internal ~h_name h_proof state

let ex_falso state =
  let context = PC_ExFalso (to_judgement $ goal state, context state) in
  let goal = (goal_env state, F_Bot) in
  unfinished goal context

let truth state =
  let env = goal_env state in
  match goal_formula state with
  | F_Top -> find_goal_in_ctx (proof_axiom env F_Top) (context state)
  | f     -> raise $ formula_mismatch F_Top f

let by_solver state =
  let env, f = goal state in
  let ctx = context state in
  let proof_env = ProofEnv.map_assumptions snd env in
  match f with
  | F_Constr c          ->
      let c_proof = proof_constr proof_env c in
      find_goal_in_ctx c_proof ctx
  | F_ConstrAnd (c, f') ->
      let c_proof = proof_constr proof_env c in
      let f_proof = proof_hole (env |> add_constr c) f' in
      let jgmt = to_judgement (env, f) in
      find_goal_in_proof ctx $ proof_constr_and jgmt c_proof f_proof
  | f                   -> raise $ not_a_constraint f

let qed = finish

let generalize name state =
  let env, f = goal state in
  match ProofEnv.lookup_identifier name env with
  | Some (a, K_Atom)    ->
      let context = PC_SpecializeAtom (to_judgement (env, f), A a, context state) in
      unfinished (env |> remove_identifier a, F_ForallAtom (A a, f)) context
  | Some (x, K_Var)     ->
      let context = PC_SpecializeTerm (to_judgement (env, f), var (V x), context state) in
      unfinished (env |> remove_identifier x, F_ForallTerm (V x, f)) context
  | Some (_x, K_FVar _) -> raise $ ProofException "Logical variables cannot be generalized"
  | Some (_x, K_Func)   -> raise $ ProofException "Functional symbols cannot be generalized"
  | None                -> raise $ unbound_variable name

let exists witness state =
  let env = goal_env state in
  match goal_formula state with
  | F_ExistsAtom (a, f_a) as f ->
      let b = parse_atom_in_env (identifiers env) witness in
      let context = PC_ExistsAtom (to_judgement (env, f), b, context state) in
      unfinished (env, (a |-> b) f_a) context
  | F_ExistsTerm (x, f_x) as f ->
      let t = parse_term_in_env (identifiers env) witness in
      let context = PC_ExistsTerm (to_judgement (env, f), t, context state) in
      unfinished (env, (x |=> t) f_x) context
  | f                          -> raise $ not_an_exists f

let remove_assm h_name = remove_assumptions (( = ) h_name % fst)

let update_assm h_name h = remove_assm h_name %> add_assumption (h_name, h)

let destruct_assm_witness env f h_name h_proof h ctx =
  let ctx = PC_WitnessUsage (to_judgement (env, f), h_proof, ctx)
  and env = update_assm h_name h env in
  unfinished (env, f) ctx

let destruct_assm_and env f h_name hs_proof hs ctx =
  (* given [h] and current goal [f] (in context [ctx]) and return goal [h => f] in proper context *)
  let add_conjunct h (f, ctx) =
    let f = F_Impl (h, f) in
    let h_proof = proof_and_elim (to_judgement (env, h)) hs_proof in
    (f, PC_ApplyLeft (to_judgement (env, f), ctx, h_proof))
  in
  let f, ctx = List.fold_right add_conjunct hs (f, ctx) in
  let h_names = List.mapi (fun i _ -> h_name ^ "_" ^ string_of_int i) hs in
  unfinished (env, f) ctx |> intros h_names

let destruct_assm_or env f h_name hs_proof hs ctx =
  let h_env = remove_assm h_name env in
  let hs_proofs = List.map (fun h -> proof_hole h_env $ F_Impl (h, f)) hs in
  find_goal_in_proof ctx $ proof_or_elim (to_judgement (env, f)) hs_proof hs_proofs

let destruct_assm h_name state =
  let env, f = goal state in
  let h_proof = assm_proof h_name env in
  let ctx = context state in
  match label' h_proof with
  | F_ExistsTerm (V x, h_x) -> destruct_assm_witness (add_var x env) f h_name h_proof h_x ctx
  | F_ExistsAtom (A a, h_a) -> destruct_assm_witness (add_atom a env) f h_name h_proof h_a ctx
  | F_And fs                -> destruct_assm_and env f h_name h_proof fs ctx
  | F_Or fs                 -> destruct_assm_or env f h_name h_proof fs ctx
  | f                       -> raise $ cannot_destruct f

let destruct_goal state =
  let ctx = context state in
  let env, f = goal state in
  match f with
  | F_And fs            ->
      let jgmt = to_judgement (env, f) in
      let goals = List.map (proof_hole env) fs in
      find_goal_in_proof ctx $ proof_and jgmt goals
  | F_ConstrAnd (c, f') ->
      let c_proof = proof_hole env (F_Constr c) in
      let f_proof = proof_hole (env |> add_constr c) f' in
      let jgmt = to_judgement (env, f) in
      find_goal_in_proof ctx $ proof_constr_and jgmt c_proof f_proof
  | f                   -> raise $ cannot_destruct f

let destruct_goal' n state =
  let env, f = goal state in
  match f with
  | F_Or fs ->
      let g = List.nth fs n in
      let context = PC_Or (to_judgement (env, f), context state) in
      unfinished (env, g) context
  | f       -> raise $ cannot_destruct f

let by_induction y_name ind_hyp_name state =
  match goal state with
  | env, F_ForallTerm ((V x_name as x), f_x) ->
      let y = V y_name in
      let f_y = (x |=> var (V y_name)) f_x in
      let ctx = PC_Induction (to_judgement (env, f_x), x, y, context state) in
      let ind_hyp = F_ForallTerm (y, F_ConstrImpl (var y <: var x, f_y)) in
      unfinished (env |> add_var x_name |> add_assumption (ind_hyp_name, ind_hyp), f_x) ctx
  | _, f -> raise $ not_a_forall f

let step n state =
  let env, f = goal state in
  let mapping, _, f' = computeWHNF (mapping env) n f in
  let env = set_mapping mapping env in
  unfinished (env, f') $ PC_Equivalent (to_judgement (env, f), n, context state)
