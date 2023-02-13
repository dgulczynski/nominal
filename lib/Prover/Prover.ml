open Types
open Common
open IncProof
open Parser
open ProofException
open ProofEnv
open ProverGoal
open ProverInternals
open Substitution

let check_props env formulas =
  let kind_infer = KindChecker.kind_infer $ kind_checker_env env in
  let check_prop f =
    match kind_infer f with
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
  match goal_formula state with
  | F_Constr c ->
      let proof_env = ProofEnv.map_assumptions snd $ goal_env state in
      find_goal_in_ctx (proof_constr proof_env c) (context state)
  | f          -> raise $ not_a_constraint f

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

let remove_assm name = remove_assumptions (( = ) name % fst)

let destruct_assm h_name state =
  let env, f = goal state in
  let h_proof = assm_proof h_name env in
  let context = PC_WitnessUsage (to_judgement (env, f), h_proof, context state) in
  let update =
    match label' h_proof with
    | F_ExistsAtom (A a, h_a) -> remove_assm h_name %> add_assumption (h_name, h_a) %> add_atom a
    | F_ExistsTerm (V x, h_x) -> remove_assm h_name %> add_assumption (h_name, h_x) %> add_var x
    | f                       -> raise $ not_an_exists f
  in
  unfinished (update env, f) context
