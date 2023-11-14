open Types
open Substitution
open KindCheckerEnv
open Solver
open Prelude
open Permutation
open Utils

(** [solve env c] returns [[]; env |- c] *)
let solve env c = constraints_of env |-: c

let add_constr_to_kind constrs k = List.fold_left (fun k c -> K_Constr (c, k)) k constrs

(** Pushes contraints downwards in the kind tree *)
let normalize =
  let rec normalize constrs = function
    | K_Prop -> K_Prop
    | K_Constr (c, k) -> normalize (c :: constrs) k
    | K_Arrow (k1, k2) -> K_Arrow (k1, add_constr_to_kind constrs k2)
    | K_ForallTerm (x, k) -> K_ForallTerm (x, add_constr_to_kind constrs k)
    | K_ForallAtom (a, k) -> K_ForallAtom (a, add_constr_to_kind constrs k)
  in
  normalize []

let rec subkind env k1 k2 =
  match (k1, k2) with
  | k1, K_Constr (c, k2) -> add_constr env c |> (k1 <=: k2)
  | (K_Constr _ as k1), k2 -> (
    match normalize k1 with
    | K_Constr (c, k1) -> solve env c && env |> (k1 <=: k2)
    | k1 -> (k1 <=: k2) env )
  | K_Prop, K_Prop -> true
  | K_Prop, _ -> false
  | K_Arrow (k1, k1'), K_Arrow (k2, k2') -> env |> (k2 <=: k1) && env |> (k1' <=: k2')
  | K_Arrow _, _ -> false
  | K_ForallTerm (V_Bind (_, x1), k1), K_ForallTerm (V_Bind (_, x2), k2) ->
    let x = fresh_var () in
    let env = map_var (map_var env x1 x) x2 x in
    let k1 = subst_var_in_kind x1 (var x) k1 in
    let k2 = subst_var_in_kind x2 (var x) k2 in
    env |> (k1 <=: k2)
  | K_ForallTerm _, _ -> false
  | K_ForallAtom (A_Bind (_, a1), k1), K_ForallAtom (A_Bind (_, a2), k2) ->
    let a = fresh_atom () in
    let env = map_atom (map_atom env a1 a) a2 a in
    let k1 = subst_atom_in_kind a1 (pure a) k1 in
    let k2 = subst_atom_in_kind a2 (pure a) k2 in
    env |> (k1 <=: k2)
  | K_ForallAtom _, _ -> false

and ( <=: ) k1 k2 env = subkind env k1 k2

let rec kind_check env kind formula =
  match kind_infer env formula with
  | Some k -> subkind env k kind
  | None -> false

and kind_infer env = function
  | F_Var x -> find_fvar env x
  | F_Bot | F_Top | F_Constr _ -> Some K_Prop
  | F_And fs | F_Or fs -> to_option K_Prop (List.for_all (is_prop env % snd) fs)
  | F_Impl (f1, f2) -> to_option K_Prop (is_prop env f1 && is_prop env f2)
  | F_ForallTerm (_, f) | F_ForallAtom (_, f) | F_ExistsTerm (_, f) | F_ExistsAtom (_, f) ->
    to_option K_Prop (is_prop env f)
  | F_ForallForm (FV_Bind (p, i, k), f) | F_ExistsForm (FV_Bind (p, i, k), f) ->
    to_option K_Prop (is_prop (map_fvar env p (FV i) k) f)
  | F_ConstrAnd (c, f) | F_ConstrImpl (c, f) -> to_option K_Prop (is_prop (add_constr env c) f)
  | F_Fun (FV_Bind (x, i, k), f) -> (fun fk -> K_Arrow (k, fk)) <$> kind_infer (map_fvar env x (FV i) k) f
  | F_App (f1, f2) -> (
    match normalize <$> kind_infer env f1 with
    | Some (K_Arrow (k2, k)) when env |> f2 -: k2 -> Some k
    | _ -> None )
  | F_FunTerm (x, f) -> (fun k -> K_ForallTerm (x, k)) <$> kind_infer env f
  | F_AppTerm (f, t) -> (
    match normalize <$> kind_infer env f with
    | Some (K_ForallTerm (V_Bind (_, x), k)) -> Some (subst_var_in_kind x t k)
    | _ -> None )
  | F_FunAtom (a, f) -> (fun k -> K_ForallAtom (a, k)) <$> kind_infer env f
  | F_AppAtom (f, a) -> (
    match normalize <$> kind_infer env f with
    | Some (K_ForallAtom (A_Bind (_, a'), k)) -> Some (subst_atom_in_kind a' a k)
    | _ -> None )
  | F_Fix (FV_Bind (fix_name, fix, fix_k), V_Bind (x_name, x), k, f) ->
    (*  G, X : (forall y, [y < x] => K{y/x}) |- F : K  *)
    (* ----------------------------------------------- *)
    (*        G |- fix X(x). (F : K) : forall x, K     *)
    let y = fresh_var () in
    let fix_k_proper = env |> (fix_k <=: fix_kind x y (x_name ^ "'") k) in
    let env = map_fvar env fix_name (FV fix) fix_k in
    to_option (K_ForallTerm (V_Bind (x_name, x), k)) (fix_k_proper && env |> f -: k)

and is_prop env f = env |> f -: K_Prop

and ( -: ) f k env = kind_check env k f
