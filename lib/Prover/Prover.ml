open Types
open Prelude
open Parser
open Permutation
open Substitution
open Utils
open ProofCommon
open ProofEnv
open ProofEquiv
open ProofException
open IncProof
open ProverGoal
open ProverInternals

let check_props env formulas = List.iter (kind_check_throw env K_Prop) formulas

let check_input env goal =
  let assumptions = List.map snd $ assumptions env in
  check_props env $ goal :: assumptions

let proof env f =
  let _ = check_input env f in
  let goal = (env, f) in
  unfinished goal $ PC_Root (to_judgement goal)

let intro state =
  let env, f = goal state in
  let context = PC_Intro (to_judgement (env, f), context state) in
  match f with
  | F_ConstrImpl (constr, f2) -> unfinished (env |> add_constr constr, f2) context
  | F_ForallAtom (a_bind, f') -> unfinished (env |> add_atom a_bind, f') context
  | F_ForallTerm (x_bind, f') -> unfinished (env |> add_var x_bind, f') context
  | F_ForallForm (p_bind, f') -> unfinished (env |> add_fvar p_bind, f') context
  | _ -> raise_in_env env $ not_a_constr_implication f

let intros = flip (List.fold_left (flip intro_named))

let apply h state =
  let env = goal_env state in
  let _ = check_props env [h] in
  apply_internal (proof_hole env h) state

let apply_thm proof state = apply_internal (proven proof) state

let assm_proof h_name env = proof_assm env (lookup env h_name)

let apply_assm h_name state =
  let env = goal_env state in
  apply_internal ~h_name (assm_proof h_name env) state

let specialize_proof proof specs env =
  let identifiers_env = all_identifiers env in
  let specialize proof spec =
    let env, h = judgement' proof in
    let on_forall_atom (A_Bind (_, a)) f =
      let b = parse_atom_in_env identifiers_env spec in
      SpecAtom (b, (a |-> b) f)
    in
    let on_forall_term (V_Bind (_, x)) f =
      let t = parse_term_in_env identifiers_env spec in
      SpecTerm (t, (x |=> t) f)
    in
    let on_forall_form (FV_Bind (_, p, _)) f =
      let g = parse_formula_in_env identifiers_env spec in
      SpecForm (g, (FV p |==> g) f)
    in
    match specialize on_forall_atom on_forall_term on_forall_form h with
    | SpecAtom (a, f) -> proof_specialize_atom (env, f) a proof
    | SpecTerm (t, f) -> proof_specialize_term (env, f) t proof
    | SpecForm (g, f) -> proof_specialize_form (env, f) g proof
  in
  List.fold_left specialize (proof_step 5 proof) specs

let apply_assm_spec h_name specs state =
  let env = goal_env state in
  let h_proof = assm_proof h_name env in
  apply_internal ~h_name (specialize_proof h_proof specs env) state

let apply_thm_spec thm specs state =
  let thm_proof = proven thm and env = goal_env state in
  apply_internal (specialize_proof thm_proof specs env) state

let ex_falso state =
  let context = PC_ExFalso (to_judgement $ goal state, context state) in
  let goal = (goal_env state, F_Bot) in
  unfinished goal context

let solve state =
  let env, f = goal state in
  let ctx = context state in
  let proof_env = ProofEnv.map_assms snd id env in
  match f with
  | F_Constr c ->
    let c_proof = proof_constr proof_env c in
    find_goal_in_ctx c_proof ctx
  | F_ConstrAnd (c, f') ->
    let c_proof = proof_constr proof_env c in
    let f_proof = proof_hole (env |> add_constr c) f' in
    let jgmt = to_judgement (env, f) in
    find_goal_in_proof ctx $ proof_constr_and jgmt c_proof f_proof
  | F_Bot -> find_goal_in_proof ctx % proven $ Proof.constr_e (map_assms snd id env)
  | f -> raise_in_env env $ not_a_constraint f

let qed = finish

let generalize name state =
  let env, f = goal state in
  match ProofEnv.lookup_identifier name env with
  | Some (Bind (a_name, K_Atom a)) ->
    let ctx = PC_SpecializeAtom (to_judgement (env |> remove_identifier a, f), pure (A a), context state) in
    unfinished (env |> remove_identifier a, F_ForallAtom (A_Bind (a_name, A a), f)) ctx
  | Some (Bind (x_name, K_Var x)) ->
    let ctx = PC_SpecializeTerm (to_judgement (env |> remove_identifier x, f), var (V x), context state) in
    unfinished (env |> remove_identifier x, F_ForallTerm (V_Bind (x_name, V x), f)) ctx
  | Some (Bind (p_name, K_FVar (p, k))) ->
    let ctx = PC_SpecializeForm (to_judgement (env |> remove_identifier p, f), fvar p, context state) in
    unfinished (env |> remove_identifier p, F_ForallForm (FV_Bind (p_name, p, k), f)) ctx
  | Some (Bind (_x, K_Func)) -> raise $ ProofException "Functional symbols cannot be generalized"
  | None -> raise $ unbound_variable name

let exists witness state =
  let env = goal_env state in
  match goal_formula state with
  | F_ExistsAtom (A_Bind (_, a), f_a) as f ->
    let b = parse_atom_in_env (identifiers env) witness in
    let context = PC_ExistsAtom (to_judgement (env, f), b, context state) in
    unfinished (env, (a |-> b) f_a) context
  | F_ExistsTerm (V_Bind (_, x), f_x) as f ->
    let t = parse_term_in_env (identifiers env) witness in
    let context = PC_ExistsTerm (to_judgement (env, f), t, context state) in
    unfinished (env, (x |=> t) f_x) context
  | F_ExistsForm (FV_Bind (_, x, x_kind), f_x) as f ->
    let g = parse_formula_in_env (identifiers env) witness in
    kind_check_throw env x_kind g ;
    let context = PC_ExistsForm (to_judgement (env, f), g, context state) in
    unfinished (env, (FV x |==> g) f_x) context
  | f -> raise_in_env env $ not_an_exists f

let exists' witnesses state = List.fold_left (flip exists) state witnesses

let remove_assm h_name = remove_assms (( = ) h_name % fst)

let update_assm h_name h = remove_assm h_name %> add_assm (h_name, h)

let destruct_assm_witness env f h_name h_proof h witness_bind ctx =
  let ctx = PC_WitnessUsage (to_judgement (env, f), h_proof, binder_name witness_bind, ctx) in
  let env = env |> add_identifier witness_bind |> update_assm h_name h in
  unfinished (env, f) ctx

let destruct_assm_and env f h_name hs_proof hs ctx =
  (* given [h] and current goal [f] (in context [ctx]) and return goal [h => f] in proper context *)
  let add_conjunct (_, h) (f, ctx) =
    let f = F_Impl (h, f) in
    let h_proof = proof_and_elim (to_judgement (env, h)) hs_proof in
    (f, PC_ApplyLeft (to_judgement (env, f), ctx, h_proof))
  in
  let f, ctx = List.fold_right add_conjunct hs (f, ctx) in
  let h_names =
    let h_name i (case, _) = h_name ^ "_" ^ if case <> "" then case else string_of_int (succ i) in
    List.mapi h_name hs
  in
  unfinished (env, f) ctx |> intros h_names

let destruct_assm_or env f h_name hs_proof hs ctx =
  let h_env = remove_assm h_name env in
  let hs_proofs = List.map (fun (_, h) -> proof_hole h_env $ F_Impl (h, f)) hs in
  find_goal_in_proof ctx $ proof_or_elim (to_judgement (env, f)) hs_proof hs_proofs

let destruct_assm_constr_and env f h_name c_and_h_proof c h ctx =
  let c_proof = proof_constr_and_elim_left (to_judgement (env, F_Constr c)) c_and_h_proof in
  let h_proof = proof_constr_and_elim_right (to_judgement (env, h)) c_and_h_proof in
  let ctx = PC_ApplyLeft (to_judgement (env, f), ctx, c_proof) in
  let ctx = PC_ApplyLeft (to_judgement (env, F_Impl (h, f)), ctx, h_proof) in
  let jgmt = (env |> remove_assm h_name, F_ConstrImpl (c, F_Impl (h, f))) in
  unfinished jgmt ctx |> intro |> intros [h_name]

let destruct_assm_constr env f h_name h_proof c ctx =
  let ctx = PC_ApplyLeft (to_judgement (env, f), ctx, h_proof) in
  let jgmt = (env |> remove_assm h_name, F_ConstrImpl (c, f)) in
  unfinished jgmt ctx |> intro

let destruct_assm h_name state =
  let env, f = goal state in
  let h_proof = assm_proof h_name env in
  let ctx = context state in
  let env, _, h = computeWHNF env 5 $ label' h_proof in
  match h with
  | F_ExistsTerm _ ->
    let x_bind, h_x = instantiate_var h in
    destruct_assm_witness env f h_name h_proof h_x (var_binder_to_binder x_bind) ctx
  | F_ExistsAtom _ ->
    let a_bind, h_a = instantiate_atom h in
    destruct_assm_witness env f h_name h_proof h_a (atom_binder_to_binder a_bind) ctx
  | F_And hs -> destruct_assm_and env f h_name h_proof hs ctx
  | F_Or hs -> destruct_assm_or env f h_name h_proof hs ctx
  | F_ConstrAnd (c, h) -> destruct_assm_constr_and env f h_name h_proof c h ctx
  | F_Constr c -> destruct_assm_constr env f h_name h_proof c ctx
  | f -> raise_in_env env $ cannot_destruct f

let rec destruct_assm' h_name witnesses state =
  match witnesses with
  | [] -> state
  | w_name :: ws ->
    (let env, f = goal state in
     let h_proof = assm_proof h_name env in
     let ctx = context state in
     let env, _, h = computeWHNF env 5 $ label' h_proof in
     match h with
     | F_ExistsTerm _ ->
       let V_Bind (_, V x), h_x = instantiate_var h in
       destruct_assm_witness env f h_name h_proof h_x (Bind (w_name, K_Var x)) ctx
     | F_ExistsAtom _ ->
       let A_Bind (_, A a), h_a = instantiate_atom h in
       destruct_assm_witness env f h_name h_proof h_a (Bind (w_name, K_Atom a)) ctx
     | F_And hs -> destruct_assm_and env f h_name h_proof hs ctx
     | F_Or hs -> destruct_assm_or env f h_name h_proof hs ctx
     | F_ConstrAnd (c, h) -> destruct_assm_constr_and env f h_name h_proof c h ctx
     | F_Constr c -> destruct_assm_constr env f h_name h_proof c ctx
     | f -> raise_in_env env $ cannot_destruct f )
    |> destruct_assm' h_name ws

let intros' = function
  | [] -> id
  | h :: ws -> intro_named h %> destruct_assm' h ws

let destruct_goal state =
  let ctx = context state in
  let env, f = goal state in
  match f with
  | F_And fs ->
    let jgmt = to_judgement (env, f) in
    let goals = List.map (proof_hole env % snd) fs in
    find_goal_in_proof ctx $ proof_and jgmt goals
  | F_ConstrAnd (c, f') ->
    let c_proof = proof_hole env (F_Constr c) in
    let f_proof = proof_hole (env |> add_constr c) f' in
    let jgmt = to_judgement (env, f) in
    find_goal_in_proof ctx $ proof_constr_and jgmt c_proof f_proof
  | f -> raise_in_env env $ cannot_destruct f

let destruct_goal' n state =
  let env, f = goal state in
  match f with
  | F_Or fs ->
    let _, g = List.nth fs n in
    let context = PC_Or (to_judgement (env, f), context state) in
    unfinished (env, g) context
  | f -> raise_in_env env $ cannot_destruct f

let by_induction y_name ind_hyp_name state =
  match goal state with
  | env, F_ForallTerm ((V_Bind (_, x) as x_bind), f_x) ->
    let y = fresh_var () in
    let y_bind = V_Bind (y_name, y) in
    let f_y = (x |=> var y) f_x in
    let ctx = PC_Induction (to_judgement (env, f_x), x_bind, y_bind, context state) in
    let ind_hyp = F_ForallTerm (y_bind, F_ConstrImpl (var y <: var x, f_y)) in
    unfinished (env |> add_var x_bind |> add_assm (ind_hyp_name, ind_hyp), f_x) ctx
  | env, f -> raise_in_env env $ not_a_forall_term f

let step n state =
  let env, f = goal state in
  let env, _, f' = computeWHNF env n f in
  unfinished (env, f') $ PC_Equivalent (to_judgement (env, f), n, context state)

let case name state =
  let env, f = goal (step 5 state) in
  let ctx = PC_Or (to_judgement (env, f), context state) in
  match f with
  | F_Or fs -> (
    match List.find_opt (( = ) name % fst) fs with
    | Some (_, f) -> unfinished (env, f) ctx
    | None -> raise_in_env env $ unknown_case name f )
  | f -> raise_in_env env $ not_a_disjunction f

let assert_constr env constr =
  let void = const () in
  let proof_env = ProofEnv.map_assms snd id env in
  void $ IncProof.proof_constr proof_env constr

let subst x_name y_source state =
  let cannot_subst = raise % proof_exception % Printf.sprintf "Cannot substitute %s" in
  let env, f = goal state in
  match ProofEnv.lookup_identifier x_name env with
  | Some (Bind (_, K_Func)) -> cannot_subst "a functional symbol"
  | Some (Bind (_, K_FVar _)) -> cannot_subst "a logical variable"
  | None -> cannot_subst "unknown name"
  | Some (Bind (_, K_Atom a)) ->
    let b = parse_atom_in_env (all_identifiers env) y_source in
    let _ = assert_constr env (A a ==: b) in
    let ctx = PC_SubstAtom (to_judgement (env, f), A a, b, context state) in
    unfinished (ProofEnv.subst_atom (fun a b -> on_snd (a |-> b)) (A a) b env, (A a |-> b) f) ctx
  | Some (Bind (_, K_Var x)) ->
    let t = parse_term_in_env (all_identifiers env) y_source in
    let _ = assert_constr env (var (V x) =: t) in
    let ctx = PC_SubstVar (to_judgement (env, f), V x, t, context state) in
    unfinished (ProofEnv.subst_var (fun x t -> on_snd (x |=> t)) (V x) t env, (V x |=> t) f) ctx

let add_assm h_name h_proof state =
  let h = label' h_proof in
  let env, f = goal state in
  let f_state =
    unfinished (env |> remove_assm h_name, F_Impl (h, f)) (PC_Root (to_judgement (env, F_Impl (h, f))))
    |> intro_named h_name
  in
  let f_incproof = meld (uncurry proof_hole $ goal f_state) (context f_state) in
  let f_ctx = PC_ApplyRight (to_judgement (env, f), f_incproof, context state) in
  find_goal_in_proof f_ctx h_proof

let add_assm_thm' h_name h_proof state =
  let h = label' h_proof in
  let env, f = goal state in
  let ctx = PC_ApplyLeft (to_judgement (env, f), context state, h_proof) in
  unfinished (env, F_Impl (h, f)) ctx |> intro_named h_name

let add_assm_thm h_name = add_assm_thm' h_name % proven

let add_assm_thm_spec h_name h_proof specs state =
  let env, _ = goal state in
  let h_spec_proof = specialize_proof (proven h_proof) specs env in
  add_assm_thm' h_name h_spec_proof state

let specialize_assm h_name h_spec_name specs state =
  let env = goal_env state in
  let h_proof = assm_proof h_name env in
  let h_spec_proof = specialize_proof h_proof specs env in
  state |> add_assm h_spec_name h_spec_proof

let apply_in_assm h_name h_premise_name state =
  let env, _ = goal state in
  let h_proof = assm_proof h_name env in
  let h_premise_proof = assm_proof h_premise_name env in
  let h_env, h = judgement' h_proof in
  match computeWHNF h_env 5 h with
  | h_env, _, F_Impl (_, h_conclusion) ->
    let h_conclusion_proof = proof_apply (h_env, h_conclusion) h_proof h_premise_proof in
    add_assm h_name h_conclusion_proof state
  | _ -> raise_in_env env % not_an_implication $ label' h_premise_proof

let truth state =
  match goal state with
  | _, F_Top ->
    let ctx = context state in
    find_goal_in_ctx proof_truth ctx
  | env, f -> raise_in_env env $ formula_mismatch F_Top f
