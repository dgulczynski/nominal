open Common
open ProofCommon
open ProofEnv
open Solver
open Substitution
open Types

let lookup_formula env (FV x) =
  match List.find_opt (fun {bind= FV_Bind (_, y, _); _} -> x = y) (mapping env) with
  | Some {body= f; _} -> Some f
  | None              -> None

let solver_assumptions env =
  let constr_assumptions = List.filter_map (to_constr_op % to_formula env) $ assumptions env in
  constr_assumptions @ constraints env

let constr_equiv env1 env2 c1 c2 =
  let solver_assumptions = solver_assumptions env1 @ solver_assumptions env2 in
  let ( === ) t1 t2 = solver_assumptions |-: (t1 =: t2) in
  let ( =:= ) (t1, t1') (t2, t2') = (t1 === t2 && t1' === t2') || (t1 === t2' && t1' === t2) in
  match (c1, c2) with
  | C_AtomEq (a1, b1), C_AtomEq (a2, b2) | C_AtomNeq (a1, b1), C_AtomNeq (a2, b2) ->
      (atom a1, T_Atom b1) =:= (atom a2, T_Atom b2)
  | C_AtomEq (a, b), C_Eq (t1, t2) | C_Eq (t1, t2), C_AtomEq (a, b) -> (atom a, T_Atom b) =:= (t1, t2)
  | C_Shape (t1, t2), C_Shape (t1', t2') | C_Subshape (t1, t2), C_Subshape (t1', t2') | C_Eq (t1, t2), C_Eq (t1', t2')
    -> (t1, t2) =:= (t1', t2')
  | C_AtomNeq (a1, b1), C_Fresh (a2, t2) | C_Fresh (a2, t2), C_AtomNeq (a1, b1) -> (atom a1, T_Atom b1) =:= (atom a2, t2)
  | C_Fresh (a1, t1), C_Fresh (a2, t2) -> (atom a1, t1) =:= (atom a2, t2)
  | C_AtomEq _, _ | C_Shape _, _ | C_Subshape _, _ | C_AtomNeq _, _ | C_Eq _, _ | C_Fresh _, _ -> false

let rec computeWHNF env n f =
  if n <= 0 then (env, 0, f)
  else
    match f with
    | F_Top
    | F_Bot
    | F_And _
    | F_Or _
    | F_Impl _
    | F_Constr _
    | F_ConstrAnd _
    | F_ConstrImpl _
    | F_ForallTerm _
    | F_ForallAtom _
    | F_ExistsTerm _
    | F_ExistsAtom _
    | F_Fun _
    | F_FunTerm _
    | F_FunAtom _
    | F_Fix _ -> (env, n, f)
    | F_Var x -> (
      match lookup_formula env x with
      | Some f -> computeWHNF env (n - 1) <| f
      | None   -> (env, n, f) )
    | F_AppTerm (f, t) -> (
      match computeWHNF env n f with
      | env, n, F_FunTerm (x, f) when n > 0 -> computeWHNF env (n - 1) <| (x |=> t) f
      | env, n, (F_Fix (bind, x, _, f) as body) when n > 0 ->
          let env = add_to_mapping env {bind; body} in
          computeWHNF env (n - 1) <| (x |=> t) f
      | env, n, f -> (env, n, F_AppTerm (f, t)) )
    | F_AppAtom (f, b) -> (
      match computeWHNF env n f with
      | env, n, F_FunAtom (a, f) when n > 0 -> computeWHNF env (n - 1) <| (a |-> b) f
      | env, n, f -> (env, n, F_AppAtom (f, b)) )
    | F_App (f1, f2) -> (
      match computeWHNF env n f1 with
      | env, n, (F_Fun (FV_Bind (_, x, _), f) as f1) when n > 1 -> (
        match computeWHNF env n f2 with
        | env, 0, f2 -> (env, 0, F_App (f1, f2))
        | env, n, f2 -> computeWHNF env (n - 1) <| (x |==> f2) f )
      | env, n, f1 -> (env, n, F_App (f1, f2)) )

and equiv env1 env2 n1 n2 f1 f2 =
  equiv_syntactic env1 env2 n1 n2 f1 f2
  ||
  let env1, n1, f1 = computeWHNF env1 n1 f1 in
  let env2, n2, f2 = computeWHNF env2 n2 f2 in
  let ( === ) = equiv env1 env2 n1 n2 in
  match (f1, f2) with
  | F_Top, _ | F_Bot, _ -> f1 = f2
  | F_Var x1, F_Var x2 -> (
    match (lookup_formula env1 x1, lookup_formula env1 x2) with
    | Some f1, Some f2 -> f1 === f2
    | Some f1, None    -> f1 === f2
    | None, Some f2    -> f1 === f2
    | None, None       -> x1 = x2 )
  | F_Var x1, f2 -> (
    match lookup_formula env1 x1 with
    | Some f1 -> f1 === f2
    | None    -> false (* f2 is not a fvar*) )
  | f1, F_Var x2 -> (
    match lookup_formula env2 x2 with
    | Some f2 -> f1 === f2
    | None    -> false (* f1 is not a fvar*) )
  | F_And f1s, F_And f2s | F_Or f1s, F_Or f2s -> List.for_all2 (fun (_, f1) (_, f2) -> f1 === f2) f1s f2s
  | F_And _, _ | F_Or _, _ -> false
  | F_Constr c1, F_Constr c2 -> constr_equiv env1 env2 c1 c2
  | F_Constr _, _ -> false
  | F_ConstrImpl (c1, f1'), F_ConstrImpl (c2, f2') | F_ConstrAnd (c1, f1'), F_ConstrAnd (c2, f2') ->
      constr_equiv env1 env2 c1 c2 && equiv (add_constr c1 env1) (add_constr c1 env1) n1 n2 f1' f2'
      (* analyse "dead" branches? *)
      (* || not $ constr_equiv to_formula env1 env2 c1 c2 *)
      (* && not $ Solver.solve_with_assumptions (constraints env1) c1 *)
      (* && not $ Solver.solve_with_assumptions (constraints env2) c2 *)
  | F_ConstrImpl _, _ | F_ConstrAnd _, _ -> false
  | F_Impl (f1, f1'), F_Impl (f2, f2') -> f1 === f2 && f1' === f2'
  | F_Impl _, _ -> false
  | F_ForallAtom (a1, f1), F_ForallAtom (a2, f2)
  | F_ExistsAtom (a1, f1), F_ExistsAtom (a2, f2)
  | F_FunAtom (a1, f1), F_FunAtom (a2, f2) ->
      let a = fresh_atom () in
      (a1 |-> a) f1 === (a2 |-> a) f2
  | F_ForallTerm (x1, f1), F_ForallTerm (x2, f2)
  | F_ExistsTerm (x1, f1), F_ExistsTerm (x2, f2)
  | F_FunTerm (x1, f1), F_FunTerm (x2, f2) ->
      let x = var (fresh_var ()) in
      (x1 |=> x) f1 === (x2 |=> x) f2
  | F_ForallAtom _, _ | F_ForallTerm _, _ | F_ExistsAtom _, _ | F_ExistsTerm _, _ | F_FunTerm _, _ | F_FunAtom _, _ ->
      false
  | F_Fun (FV_Bind (_, x1, k1), f1), F_Fun (FV_Bind (_, x2, k2), f2) ->
      k1 = k2
      &&
      let x = fresh_fvar () in
      (x1 |==> F_Var x) f1 === (x2 |==> F_Var x) f2
  | F_Fun _, _ -> false
  | F_Fix (FV_Bind (_, fix1, fix1_k), x1, x1_k, f1), F_Fix (FV_Bind (_, fix2, fix2_k), x2, x2_k, f2) ->
      fix1_k = fix2_k && x1_k = x2_k
      &&
      let x = fresh_var () and fix = fresh_fvar () in
      let sub1 = (x1 |=> var x) % (fix1 |==> F_Var fix) in
      let sub2 = (x2 |=> var x) % (fix2 |==> F_Var fix) in
      sub1 f1 === sub2 f2
  | F_Fix _, _ -> false
  | F_App (f1, f1'), F_App (f2, f2') ->
      (* we are after computeWNHF so we don't do any substitutions *)
      f1 === f2 && f1' === f2'
  | F_AppAtom (f1, a1), F_AppAtom (f2, a2) ->
      (* we are after computeWNHF so we don't do any substitutions *)
      a1 = a2 && f1 === f2
  | F_AppTerm (f1, t1), F_AppTerm (f2, t2) ->
      (* we are after computeWNHF so we don't do any substitutions *)
      t1 = t2 && f1 === f2
  | F_App _, _ | F_AppAtom _, _ | F_AppTerm _, _ -> false

and equiv_syntactic env1 env2 n1 n2 f1 f2 =
  let ( === ) = equiv_syntactic env1 env2 n1 n2 in
  match (f1, f2) with
  | F_Top, _ | F_Bot, _ -> f1 = f2
  | F_Var x1, F_Var x2 -> (
    match (lookup_formula env1 x1, lookup_formula env2 x2) with
    | Some f1, Some f2 -> f1 === f2
    | Some f1, None    -> f1 === f2
    | None, Some f2    -> f1 === f2
    | None, None       -> x1 = x2 )
  | F_Var x1, f2 -> (
    match lookup_formula env1 x1 with
    | Some f1 -> f1 === f2
    | None    -> false (* f2 is not a fvar*) )
  | f1, F_Var x2 -> (
    match lookup_formula env2 x2 with
    | Some f2 -> f1 === f2
    | None    -> false (* f1 is not a fvar*) )
  | F_And f1s, F_And f2s | F_Or f1s, F_Or f2s -> List.for_all2 (fun (_, f1) (_, f2) -> f1 === f2) f1s f2s
  | F_And _, _ | F_Or _, _ -> false
  | F_Constr c1, F_Constr c2 -> c1 = c2
  | F_Constr _, _ -> false
  | F_ConstrImpl (c1, f1), F_ConstrImpl (c2, f2) | F_ConstrAnd (c1, f1), F_ConstrAnd (c2, f2) -> c1 = c2 && f1 === f2
  | F_ConstrImpl _, _ | F_ConstrAnd _, _ -> false
  | F_Impl (f1, f1'), F_Impl (f2, f2') -> f1 === f2 && f1' === f2'
  | F_Impl _, _ -> false
  | F_ForallAtom (a1, f1), F_ForallAtom (a2, f2)
  | F_ExistsAtom (a1, f1), F_ExistsAtom (a2, f2)
  | F_FunAtom (a1, f1), F_FunAtom (a2, f2) ->
      let a = fresh_atom () in
      (a1 |-> a) f1 === (a2 |-> a) f2
  | F_ForallTerm (x1, f1), F_ForallTerm (x2, f2)
  | F_ExistsTerm (x1, f1), F_ExistsTerm (x2, f2)
  | F_FunTerm (x1, f1), F_FunTerm (x2, f2) ->
      let x = var (fresh_var ()) in
      (x1 |=> x) f1 === (x2 |=> x) f2
  | F_Fun (FV_Bind (_, x1, k1), f1), F_Fun (FV_Bind (_, x2, k2), f2) ->
      k1 = k2
      &&
      let x = fresh_fvar () in
      (x1 |==> F_Var x) f1 === (x2 |==> F_Var x) f2
  | F_ForallAtom _, _ | F_ForallTerm _, _ | F_ExistsAtom _, _ | F_ExistsTerm _, _ | F_FunTerm _, _ | F_FunAtom _, _ ->
      false
  | F_App (f1, f1'), F_App (f2, f2') -> f1 === f2 && f1' === f2'
  | F_App _, _ -> false
  | F_AppAtom (f1, a1), F_AppAtom (f2, a2) -> a1 = a2 && f1 === f2
  | F_AppTerm (f1, t1), F_AppTerm (f2, t2) -> t1 = t2 && f1 === f2
  | F_AppAtom _, _ | F_AppTerm _, _ -> false
  | F_Fun _, _ -> false
  | F_Fix (FV_Bind (_, fix1, fix1_k), x1, x1_k, f1), F_Fix (FV_Bind (_, fix2, fix2_k), x2, x2_k, f2) ->
      fix1_k = fix2_k && x1_k = x2_k
      &&
      let x = fresh_var () and fix = fresh_fvar () in
      let sub1 = (x1 |=> var x) % (fix1 |==> F_Var fix) in
      let sub2 = (x2 |=> var x) % (fix2 |==> F_Var fix) in
      sub1 f1 === sub2 f2
  | F_Fix _, _ -> false

and ( === ) f1 f2 env =
  let n = 10 (* Arbitrary depth of WHNF computation for equiv *) in
  equiv env env n n f1 f2

and add_to_mapping env {bind= FV_Bind (_, x, _) as bind; body} =
  match lookup_formula env (FV x) with
  | Some f when equiv_syntactic env env 1 1 f body -> env
  | _ -> env |> set_mapping (List.merge compare (mapping env) [{bind; body}])

let ( =/= ) f1 f2 = not % (f1 === f2)
