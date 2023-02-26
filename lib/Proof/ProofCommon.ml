open Common
open ProofException
open Substitution
open Types

type formula_mapping = {bind: fvar_binder; body: formula}

type mapping = formula_mapping list

let lookup_formula mapping (FV x) =
  match List.find_opt (fun {bind= FV_Bind (_, y, _); _} -> x = y) mapping with
  | Some {body= f; _} -> Some f
  | None              -> None

let to_constr_op = function
  | F_Constr c -> Some c
  | _          -> None

let to_constr f =
  match to_constr_op f with
  | Some c -> c
  | None   -> raise $ not_a_constraint f

let premise = function
  | F_Impl (p, _)       -> p
  | F_ConstrImpl (c, _) -> F_Constr c
  | f                   -> raise $ not_an_implication f

let conclusion = function
  | F_Impl (_, c) | F_ConstrImpl (_, c) -> c
  | f -> raise $ not_an_implication f

let disjuncts = function
  | F_Or fs -> fs
  | f       -> raise $ not_a_disjunction f

let rec computeWHNF mapping n f =
  if n <= 0 then (mapping, 0, f)
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
    | F_Fix _ -> (mapping, n, f)
    | F_Var x -> (
      match lookup_formula mapping x with
      | Some f -> computeWHNF mapping (n - 1) <| f
      | None   -> (mapping, n, f) )
    | F_AppTerm (f, t) -> (
      match computeWHNF mapping n f with
      | mapping, n, F_FunTerm (x, f) when n > 0 -> computeWHNF mapping (n - 1) <| (x |=> t) f
      | mapping, n, (F_Fix (bind, x, _, f) as body) when n > 0 ->
          let mapping = List.merge compare mapping [{bind; body}] in
          computeWHNF mapping (n - 1) <| (x |=> t) f
      | mapping, n, f -> (mapping, n, F_AppTerm (f, t)) )
    | F_AppAtom (f, b) -> (
      match computeWHNF mapping n f with
      | mapping, n, F_FunAtom (a, f) when n > 0 -> computeWHNF mapping (n - 1) <| (a |-> b) f
      | mapping, n, f -> (mapping, n, F_AppAtom (f, b)) )
    | F_App (f1, f2) -> (
      match computeWHNF mapping n f1 with
      | mapping, n, (F_Fun (FV_Bind (_, x, _), f) as f1) when n > 1 -> (
        match computeWHNF mapping n f2 with
        | mapping, 0, f2 -> (mapping, 0, F_App (f1, f2))
        | mapping, n, f2 -> computeWHNF mapping (n - 1) <| (x |==> f2) f )
      | mapping, n, f1 -> (mapping, n, F_App (f1, f2)) )

let rec equiv mapping1 mapping2 n1 n2 f1 f2 =
  let mapping1, n1, f1 = computeWHNF mapping1 n1 f1 in
  let mapping2, n2, f2 = computeWHNF mapping2 n2 f2 in
  let ( === ) = equiv mapping1 mapping2 n1 n2 in
  match (f1, f2) with
  | F_Top, F_Top | F_Bot, F_Bot -> true
  | F_Top, _ | F_Bot, _ -> false
  | F_Var x1, F_Var x2 -> (
    match (lookup_formula mapping1 x1, lookup_formula mapping1 x2) with
    | Some f1, Some f2 -> f1 === f2
    | Some f1, None    -> f1 === f2
    | None, Some f2    -> f1 === f2
    | None, None       -> x1 = x2 )
  | F_Var _, _ -> false
  | F_And f1s, F_And f2s | F_Or f1s, F_Or f2s -> List.for_all2 ( === ) f1s f2s
  | F_And _, _ | F_Or _, _ -> false
  | F_Constr c1, F_Constr c2 -> c1 = c2
  | F_Constr _, _ -> false
  | F_ConstrImpl (c1, f1), F_ConstrImpl (c2, f2) | F_ConstrAnd (c1, f1), F_ConstrAnd (c2, f2) ->
      c1 = c2 && f1 === f2
  | F_ConstrImpl _, _ | F_ConstrAnd _, _ -> false
  | F_Impl (f1, f1'), F_Impl (f2, f2') -> f1 === f2 && f1' === f2'
  | F_Impl _, _ -> false
  | F_ForallAtom (a1, f1), F_ForallAtom (a2, f2) | F_ExistsAtom (a1, f1), F_ExistsAtom (a2, f2) ->
      let a = fresh_atom () in
      (a1 |-> a) f1 === (a2 |-> a) f2
  | F_ForallTerm (x1, f1), F_ForallTerm (x2, f2) | F_ExistsTerm (x1, f1), F_ExistsTerm (x2, f2) ->
      let x = var (fresh_var ()) in
      (x1 |=> x) f1 === (x2 |=> x) f2
  | F_ForallAtom _, _ | F_ForallTerm _, _ | F_ExistsAtom _, _ | F_ExistsTerm _, _ -> false
  | F_App _, _ | F_AppAtom _, _ | F_AppTerm _, _ ->
      f1 = f2 (* we've reached recursion depth: now we only check for structural equality*)
  | F_Fun _, _ | F_FunTerm _, _ | F_FunAtom _, _ -> false
  | F_Fix _, _ -> false

and ( === ) f1 f2 mapping =
  let n = 10 (* Arbitrary depth of WHNF computation for equiv *) in
  equiv mapping mapping n n f1 f2

let ( =/= ) f1 f2 = not % (f1 === f2)
