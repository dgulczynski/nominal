open Types
open Prelude
open Permutation
open Substitution
open Solver
open KindChecker
open ProofCommon
open ProofEnv
open ProofEquiv
open ProofException

type proof_env = formula env

type judgement = proof_env * formula

type proof =
  | P_Ax of judgement
  | P_Intro of judgement * proof
  | P_Apply of judgement * proof * proof
  | P_ConstrApply of judgement * proof * proof
  | P_ConstrAndElim of judgement * proof
  | P_SpecializeAtom of judgement * permuted_atom * proof
  | P_SpecializeTerm of judgement * term * proof
  | P_SpecializeForm of judgement * formula * proof
  | P_Witness of judgement * proof * proof
  | P_AndIntro of judgement * proof list
  | P_AndElim of judgement * proof
  | P_OrElim of judgement * proof list
  | P_Equivalent of judgement * int * proof
  | P_ExFalso of judgement * proof

let label = function
  | P_Ax (_, f)
  | P_Intro ((_, f), _)
  | P_Apply ((_, f), _, _)
  | P_ConstrApply ((_, f), _, _)
  | P_ConstrAndElim ((_, f), _)
  | P_SpecializeAtom ((_, f), _, _)
  | P_SpecializeTerm ((_, f), _, _)
  | P_SpecializeForm ((_, f), _, _)
  | P_Witness ((_, f), _, _)
  | P_AndIntro ((_, f), _)
  | P_AndElim ((_, f), _)
  | P_OrElim ((_, f), _)
  | P_Equivalent ((_, f), _, _)
  | P_ExFalso ((_, f), _) -> f

let env = function
  | P_Ax (e, _)
  | P_Intro ((e, _), _)
  | P_Apply ((e, _), _, _)
  | P_ConstrApply ((e, _), _, _)
  | P_ConstrAndElim ((e, _), _)
  | P_SpecializeAtom ((e, _), _, _)
  | P_SpecializeTerm ((e, _), _, _)
  | P_SpecializeForm ((e, _), _, _)
  | P_Witness ((e, _), _, _)
  | P_AndIntro ((e, _), _)
  | P_AndElim ((e, _), _)
  | P_OrElim ((e, _), _)
  | P_Equivalent ((e, _), _, _)
  | P_ExFalso ((e, _), _) -> e

let judgement proof = (env proof, label proof)

let assumption env f = P_Ax (ProofEnv.env (identifiers env) (constraints env) [f] (mapping env) id, f)

let remove_assms_equiv_to to_formula f env = remove_assms (fun g -> f === to_formula g <| env) env

let remove_assm = remove_assms_equiv_to id

let imp_i f p =
  let f' = label p in
  let env = env p |> remove_assm f in
  P_Intro ((env, F_Impl (f, f')), p)

let raise_in_env env exn = raise % exn $ all_identifiers env

let imp_e p1 p2 =
  let env = union (env p1) (env p2) in
  match (label p1, label p2) with
  | f1, f2 when f2 === premise f1 <| env -> P_Apply ((env, conclusion f1), p1, p2)
  | f1, f2 -> raise_in_env env $ premise_mismatch f1 f2

let solver_proof (env, f) solver_goal on_solved =
  let constr_assms = List.filter_map to_constr_op $ assumptions env in
  let assumptions = List.map (fun c -> F_Constr c) constr_assms in
  let env = ProofEnv.env (identifiers env) (constraints env) assumptions (mapping env) id in
  let solver_assms = constr_assms @ constraints env in
  match solver_assms |-: solver_goal with
  | true -> on_solved (env, f)
  | false -> raise_in_env env $ solver_failure solver_assms f

let constr_i env constr =
  let judgement = (env, F_Constr constr) in
  solver_proof judgement constr $ fun jgmt -> P_Ax jgmt

let constr_e env =
  let judgement = (env, F_Bot) in
  solver_proof judgement Solver.absurd % const $ P_Ax judgement

let constr_imp_i c p =
  let f = label p in
  let env = env p |> remove_constraints (( = ) c) |> remove_assm (F_Constr c) in
  P_Intro ((env, F_ConstrImpl (c, f)), p)

let constr_imp_e c_proof c_imp_proof =
  let c = to_constr $ label c_proof in
  match label c_imp_proof with
  | F_ConstrImpl (_c, f) when _c = c ->
    let env = union (env c_proof) (env c_imp_proof) in
    P_ConstrApply ((env, f), c_proof, c_imp_proof)
  | f -> raise_in_env (env c_proof) $ premise_mismatch (F_Constr c) f

let constr_and_i c_proof f_proof =
  match judgement c_proof with
  | c_env, F_Constr c ->
    let f_env, f = judgement f_proof in
    let env = f_env |> remove_constraints (( = ) c) |> union c_env in
    P_AndIntro ((env, F_ConstrAnd (c, f)), [c_proof; f_proof])
  | env, c -> raise_in_env env $ not_a_constraint c

let constr_and_e_left c_and_proof =
  match judgement c_and_proof with
  | env, F_ConstrAnd (_, f) ->
    if f -: K_Prop <| kind_checker_env env then
      P_ConstrAndElim ((env, f), c_and_proof)
    else
      raise_in_env env $ not_a_prop f
  | env, f -> raise_in_env env $ not_a_constr_and f

let constr_and_e_right c_and_proof =
  match judgement c_and_proof with
  | env, F_ConstrAnd (c, _) -> P_ConstrAndElim ((env, F_Constr c), c_and_proof)
  | env, f -> raise_in_env env $ not_a_constr_and f

let bot_e f p =
  match judgement p with
  | env, F_Bot -> P_ExFalso ((env, f), p)
  | env, f' -> raise_in_env env $ formula_mismatch F_Bot f'

let forall_atom_i (A_Bind (a_name, A a) as a_bind) p =
  let env, f = judgement p in
  match env |> find_bind a_name with
  | None -> P_Intro ((env |> remove_identifier a, F_ForallAtom (a_bind, f)), p)
  | Some f -> raise_in_env env $ cannot_generalize a_name f

let forall_atom_e b p =
  let env, f = judgement p in
  let on_forall_atom (A_Bind (_, a)) f = SpecAtom (b, (a |-> b) f) in
  let on_forall_term _ = raise_in_env env % not_a_forall_atom in
  let on_forall_form _ = raise_in_env env % not_a_forall_atom in
  match specialize on_forall_atom on_forall_term on_forall_form f with
  | SpecAtom (b, f) -> P_SpecializeAtom ((env, f), b, p)
  | SpecTerm (_, f) | SpecForm (_, f) -> raise_in_env env $ not_a_forall_atom f

let forall_term_i (V_Bind (x_name, V x) as x_bind) p =
  let env, f = judgement p in
  match env |> find_bind x_name with
  | None -> P_Intro ((env |> remove_identifier x, F_ForallTerm (x_bind, f)), p)
  | Some f -> raise_in_env env $ cannot_generalize x_name f

let forall_term_e t p =
  let env, f = judgement p in
  let on_forall_atom _ = raise_in_env env % not_a_forall_term in
  let on_forall_form _ = raise_in_env env % not_a_forall_term in
  let on_forall_term (V_Bind (_, x)) f = SpecTerm (t, (x |=> t) f) in
  match specialize on_forall_atom on_forall_term on_forall_form f with
  | SpecTerm (t, f) -> P_SpecializeTerm ((env, f), t, p)
  | SpecAtom (_, f) | SpecForm (_, f) -> raise_in_env env $ not_a_forall_term f

let forall_form_i (FV_Bind (x_name, x, _) as x_bind) p =
  let env, f = judgement p in
  match env |> find_bind x_name with
  | None -> P_Intro ((env |> remove_identifier x, F_ForallForm (x_bind, f)), p)
  | Some f -> raise_in_env env $ cannot_generalize x_name f

let forall_form_e g p =
  let env, f = judgement p in
  let on_forall_atom _ = raise_in_env env % not_a_forall_form in
  let on_forall_term _ = raise_in_env env % not_a_forall_form in
  let on_forall_form (FV_Bind (_, x, _)) f = SpecForm (g, (FV x |==> g) f) in
  match specialize on_forall_atom on_forall_term on_forall_form f with
  | SpecForm (g, f) -> P_SpecializeForm ((env, f), g, p)
  | SpecAtom (_, f) | SpecTerm (_, f) -> raise_in_env env $ not_a_forall_form f

let exists_atom_i (A_Bind (_, A a) as a_bind) b f_a p =
  let f = (A a |-> b) f_a in
  let env, f' = judgement p in
  if f === f' <| env then
    let env = env |> remove_identifier a |> remove_assm f_a in
    P_Intro ((env, F_ExistsAtom (a_bind, f_a)), p)
  else
    raise_in_env env $ formula_mismatch f f'

let exists_term_i (V_Bind (_, V x) as x_bind) t f_x p =
  let f = (V x |=> t) f_x in
  let env, f' = judgement p in
  if f === f' <| env then
    let env = env |> remove_identifier x |> remove_assm f_x in
    P_Intro ((env, F_ExistsTerm (x_bind, f_x)), p)
  else
    raise_in_env env $ formula_mismatch f f'

let exists_form_i (FV_Bind (_, x, x_kind) as x_bind) g f_x p =
  let f = (FV x |==> g) f_x in
  let env, f' = judgement p in
  kind_check_throw env x_kind g ;
  equiv_check_throw env f f' ;
  let env = env |> remove_identifier x |> remove_assm f_x in
  P_Intro ((env, F_ExistsForm (x_bind, f_x)), p)

let exist_e p_exists witness p =
  let env, f = judgement p in
  let remove_witness = function
    | F_ExistsTerm (V_Bind (_, x), f_x) -> (
      match Utils.bind_by_name witness (identifiers env) with
      | Some (Bind (_, K_Var w)) -> remove_identifier w %> remove_assm ((x |=> var (V w)) f_x)
      | _ -> failwith ("not a var " ^ witness) )
    | F_ExistsAtom (A_Bind (_, a), f_a) -> (
      match Utils.bind_by_name witness (identifiers env) with
      | Some (Bind (_, K_Atom w)) -> remove_identifier w %> remove_assm ((a |-> pure (A w)) f_a)
      | _ -> failwith ("not an atom " ^ witness) )
    | F_ExistsForm (FV_Bind (_, x, x_kind), f_x) -> (
      match Utils.bind_by_name witness (identifiers env) with
      | Some (Bind (_, K_FVar (w, w_kind))) ->
        if x_kind <=: w_kind <| kind_checker_env env then
          remove_identifier w %> remove_assm ((FV x |==> fvar w) f_x)
        else
          raise_in_env env % formula_kind_mismatch (fvar w) x_kind $ Some x_kind
      | _ -> failwith ("not a fvar" ^ witness) )
    | g -> raise_in_env env $ not_an_exists g
  in
  let env_x, f_x = judgement p_exists in
  P_Witness ((env |> union env_x |> remove_witness f_x, f), p_exists, p)

let merge_envs = List.fold_left (flip $ union % env) $ empty id

let and_i = function
  | [] | [_] -> raise $ ProofException "Cannot introduce conjunction with less than two conjuncts"
  | ps ->
    let f = F_And (List.map (pair "" % label) ps) in
    P_AndIntro ((merge_envs ps, f), ps)

let and_e f p_fs =
  match judgement p_fs with
  | _, F_And [] | _, F_And [_] -> raise $ ProofException "Cannot eliminate conjunction with less than two conjuncts"
  | env, F_And fs when List.exists (fun (_, g) -> f === g <| env) fs -> P_AndElim ((env, f), p_fs)
  | env, g -> raise_in_env env $ not_a_conjunction_with f g

let or_i disjuncts p =
  match disjuncts with
  | [] | [_] -> raise $ ProofException "Cannot introduce disjunction with less than two disjuncts"
  | fs -> (
    match judgement p with
    | env, f when List.exists (fun (_, g) -> f === g <| env) fs -> P_Intro ((env, F_Or fs), p)
    | env, f -> raise_in_env env % not_a_disjunction_with f $ F_Or fs )

let or_e or_proof ps =
  match ps with
  | [] | [_] -> raise $ ProofException "Cannot eliminate disjunction with less than two disjuncts"
  | p :: _ ->
    let _, _, disjunction = uncurry (flip computeWHNF 10) $ judgement or_proof in
    let c = conclusion $ label p in
    let fs = disjuncts disjunction in
    let test_proof f p =
      let env, f' = judgement p in
      f' === F_Impl (f, c) <| env
    in
    if forall2 (test_proof % snd) fs ps then
      P_OrElim ((merge_envs (or_proof :: ps), c), ps)
    else
      let f = F_Or (List.map (pair "" % premise % label) ps) in
      let env, disjunction = judgement or_proof in
      raise_in_env env $ formula_mismatch disjunction f

let induction_e (V_Bind (x_name, V x) as x_bind) (V_Bind (y_name, V y)) p =
  let f_x = label p in
  let f_y = (V x |=> var (V y)) f_x in
  let ind_hyp = F_ForallTerm (V_Bind (y_name, V y), F_ConstrImpl (var (V y) <: var (V x), f_y)) in
  let env = env p |> remove_assm ind_hyp in
  match List.filter_map (fun v -> find_bind v env) [x_name; y_name] with
  | [] -> P_Intro ((env |> remove_identifier x, F_ForallTerm (x_bind, f_x)), p)
  | f :: _ ->
    raise_in_env env
    $ cannot_generalize (x_name ^ "(" ^ string_of_int x ^ ")" ^ " or " ^ y_name ^ "(" ^ string_of_int y ^ ")") f

let env_inclusion env sub_env super_env =
  List.for_all (fun h -> List.exists (fun h' -> h ==== h' <| env) (assumptions super_env)) (assumptions sub_env)
  &&
  let solver_assms = solver_env super_env in
  List.for_all (fun c -> solver_assms |-: c) (constraints sub_env)

let equivalent jgmt n p =
  let env, f = jgmt in
  let ( <= ) = env_inclusion env in
  let _, _, fn = computeWHNF env n f in
  let enve, fe = judgement p in
  if fn === fe <| env && enve <= env then P_Equivalent ((env, f), n, p) else raise_in_env env $ formula_mismatch f fe

let sub_constr sub constr =
  match sub $ F_Constr constr with
  | F_Constr constr' -> constr'
  | f -> raise $ not_a_constraint f []

let sub_env sub = map_assms sub id % map_constraints (sub_constr sub)

let subst env f sub constr p =
  let ( <= ) = env_inclusion env in
  let on_solved jgmt =
    let sub_env, sub_f = (sub_env sub env, sub f) in
    let p_env, p_f = judgement p in
    if sub_f ==== p_f <| env && p_env <= sub_env then
      P_Equivalent (jgmt, equiv_depth, p)
    else
      raise_in_env env $ formula_mismatch f p_f
  in
  solver_proof (env, f) constr on_solved

let subst_atom a b (env, f) = subst env f (a |-> b) (a ==: b)

let subst_var x t (env, f) = subst env f (x |=> t) (var x =: t)

let truth_i = P_Ax (empty id, F_Top)

module Axiom = struct
  let axiom_env = empty id

  let axiom f = P_Ax (axiom_env, f)

  let parse_axiom = axiom % parse_formula axiom_env

  let compare_atoms = parse_axiom "forall a b : atom. same: (a = b) ∨ different: (a =/= b)"

  let exists_fresh = parse_axiom "forall t : term. exists a : atom. a # t"

  let term_inversion =
    parse_axiom
    $ unwords
        [ "forall e : term."
        ; "  atom: (exists a : atom. e = a)"
        ; "  ∨"
        ; "  lam: (exists a : atom. exists e' : term. e = a.e')"
        ; "  ∨"
        ; "  app: (exists e1 e2 : term. e = e1 e2)"
        ; "  ∨"
        ; "  symbol: (symbol e)" ]
end
