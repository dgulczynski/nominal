open Common
open ProofException
open Substitution
open Types

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

let rec equiv f1 f2 =
  match (f1, f2) with
  | F_Top, F_Top | F_Bot, F_Bot -> true
  | F_Top, _ | F_Bot, _ -> false
  | F_Var x1, F_Var x2 -> x1 = x2
  | F_Var _, _ -> false
  | F_And f1s, F_And f2s | F_Or f1s, F_Or f2s -> List.for_all2 equiv f1s f2s
  | F_And _, _ | F_Or _, _ -> false
  | F_Constr c1, F_Constr c2 -> c1 = c2
  | F_Constr _, _ -> false
  | F_ConstrImpl (c1, f1), F_ConstrImpl (c2, f2) -> c1 = c2 && f1 === f2
  | F_ConstrImpl _, _ -> false
  | F_Impl (f1, f1'), F_Impl (f2, f2') -> f1 === f2 && f1' === f2'
  | F_Impl _, _ -> false
  | F_ForallAtom (a1, f1), F_ForallAtom (a2, f2) | F_ExistsAtom (a1, f1), F_ExistsAtom (a2, f2) ->
      let a = fresh_atom () in
      (a1 |-> a) f1 === (a2 |-> a) f2
  | F_ForallTerm (x1, f1), F_ForallTerm (x2, f2) | F_ExistsTerm (x1, f1), F_ExistsTerm (x2, f2) ->
      let x = var (fresh_var ()) in
      (x1 |=> x) f1 === (x2 |=> x) f2
  | F_ForallAtom _, _ | F_ForallTerm _, _ | F_ExistsAtom _, _ | F_ExistsTerm _, _ -> false
  | _ -> f1 = f2
(* | _ -> failwith $ Printf.sprintf "unimplemented: %s === %s" (Printing.string_of_formula f1)
   (Printing.string_of_formula f2) *)

and ( === ) f1 f2 = equiv f1 f2

let ( =/= ) = not %% ( === )

let rec compute n f =
  if n <= 0 then (0, f)
  else
    match f with
    | F_Top
    | F_Bot
    | F_Constr _
    | F_ForallTerm _
    | F_ForallAtom _
    | F_ExistsTerm _
    | F_ExistsAtom _
    | F_Fun _
    | F_FunTerm _
    | F_FunAtom _
    | F_Fix _
    | F_Var _ -> (n, f)
    | F_And fs ->
        let n, fs = List.fold_left_map compute n fs in
        (n, F_And fs)
    | F_Or fs ->
        let n, fs = List.fold_left_map compute n fs in
        (n, F_Or fs)
    | F_Impl (f1, f2) ->
        let n, f1 = compute n f1 in
        let n, f2 = compute n f2 in
        (n, F_Impl (f1, f2))
    | F_ConstrAnd (c, f) ->
        let n, f = compute n f in
        (n, F_ConstrAnd (c, f))
    | F_ConstrImpl (c, f) ->
        let n, f = compute n f in
        (n, F_ConstrImpl (c, f))
    | F_AppTerm (f, t) -> (
      match compute n f with
      | n, F_FunTerm (x, f) when n > 0 -> (x |=> t) f |> compute (n - 1)
      | n, (F_Fix (FV_Bind (_, fix, _), x, _, f) as fix_f) when n > 1 ->
          (x |=> t) f |> (fix |==> fix_f) |> compute (n - 2)
      | n, f -> (n, F_AppTerm (f, t)) )
    | F_AppAtom (f, b) -> (
      match compute n f with
      | n, F_FunAtom (a, f) when n > 0 -> (a |-> b) f |> compute (n - 1)
      | n, f -> (n, F_AppAtom (f, b)) )
    | F_App (f1, f2) -> (
      match compute n f1 with
      | n, (F_Fun (FV_Bind (_, x, _), f) as f1) when n > 1 -> (
        match compute n f2 with
        | 0, f2 -> (0, F_App (f1, f2))
        | n, f2 -> (x |==> f2) f |> compute (n - 1) )
      | n, f1 -> (n, F_App (f1, f2)) )
