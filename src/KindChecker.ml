open Types
open Substitution
open KindCheckerEnv
open Common

let solve env c = mem_constr env c || Solver.solve_with_assumptions (constraints_of env) c

let add_constr_to_kind constrs k = List.fold_left (fun k c -> K_Constr (c, k)) k constrs

let cast_to_arrow =
  let rec to_arrow constrs = function
    | K_Arrow (k1, k2) -> Some (K_Arrow (k1, add_constr_to_kind constrs k2))
    | K_Constr (c, k) -> to_arrow (c :: constrs) k
    | K_Prop | K_ForallAtom _ | K_ForallTerm _ -> None
  in
  to_arrow []

let cast_to_forall_atom =
  let rec to_forall_atom constrs = function
    | K_ForallAtom (a, k) -> Some (K_ForallAtom (a, add_constr_to_kind constrs k))
    | K_Constr (c, k) -> to_forall_atom (c :: constrs) k
    | K_Prop | K_Arrow _ | K_ForallTerm _ -> None
  in
  to_forall_atom []

let cast_to_forall_term =
  let rec to_forall_term constrs = function
    | K_ForallTerm (x, k) -> Some (K_ForallTerm (x, add_constr_to_kind constrs k))
    | K_Constr (c, k) -> to_forall_term (c :: constrs) k
    | K_Prop | K_Arrow _ | K_ForallAtom _ -> None
  in
  to_forall_term []

let rec subkind env k1 k2 =
  match (k1, k2) with
  | K_Prop, K_Prop -> true
  | K_Prop, _ -> false
  | K_Arrow (k1, k1'), K_Arrow (k2, k2') -> subkind env k2 k1 && subkind env k1' k2'
  | K_Arrow _, _ -> false
  | k1, K_Constr (c, k2) -> subkind (add_constr env c) k1 k2
  | K_Constr (c, k1), k2 -> solve env c && subkind env k1 k2
  | K_ForallTerm (x1, k1), K_ForallTerm (x2, k2) ->
      let x = fresh_var () in
      let env = map_var (map_var env x1 x) x2 x in
      let k1 = subst_var_in_kind x1 (var x) k1 in
      let k2 = subst_var_in_kind x2 (var x) k2 in
      subkind env k1 k2
  | K_ForallTerm _, _ -> false
  | K_ForallAtom (a1, k1), K_ForallAtom (a2, k2) ->
      let a = fresh_atom () in
      let env = map_atom (map_atom env a1 a) a2 a in
      let k1 = subst_atom_in_kind a1 a k1 in
      let k2 = subst_atom_in_kind a2 a k2 in
      subkind env k1 k2
  | K_ForallAtom _, _ -> false

let rec kind_check env kind formula =
  match (kind, formula) with
  | k, F_Var x -> (
    match find_fvar env x with
    | Some k' -> subkind env k' k
    | None    -> false )
  | k, F_App (f1, f2) -> (
    (* G |- f1 : k1 -> k3    G |- f2 : k2 *)
    (*   G |- k1 <= k2     G |- k3 <= k   *)
    (* ---------------------------------- *)
    (*           G |- f1 f2 : k           *)
    match (kind_infer env f1, kind_infer env f2) with
    | Some (K_Arrow (k1, k3)), Some k2 -> subkind env k1 k2 && subkind env k3 k
    | _                                -> false )
  | K_Prop, F_Bot | K_Prop, F_Constr _ -> true
  | K_Prop, F_And fs | K_Prop, F_Or fs -> List.for_all (kind_check env K_Prop) fs
  | K_Prop, F_Impl (f1, f2) -> kind_check env K_Prop f1 && kind_check env K_Prop f2
  | K_Prop, F_ForallTerm (_, f)
  | K_Prop, F_ExistsTerm (_, f)
  | K_Prop, F_ForallAtom (_, f)
  | K_Prop, F_ExistsAtom (_, f) -> kind_check env K_Prop f
  | K_Prop, F_ConstrImpl (c, f) | K_Prop, F_ConstrAnd (c, f) ->
      kind_check (add_constr env c) K_Prop f
  | K_Prop, _ -> false
  | K_Arrow _, F_Fun _ -> (
    match kind_infer env formula with
    | None   -> false
    | Some k -> subkind env k kind )
  | K_Arrow _, _ -> false
  | K_ForallAtom (a1, k), F_FunAtom (a2, f) ->
      let a = fresh_atom () in
      let env = map_atom (map_atom env a1 a) a2 a in
      let k = subst_atom_in_kind a1 a k in
      let f = subst_atom_in_formula a2 a f in
      kind_check env k f
  | K_ForallAtom _, _ -> false
  | K_ForallTerm (x1, k), F_FunTerm (x2, f) ->
      let x = fresh_var () in
      let env = map_var (map_var env x1 x) x2 x in
      let k = subst_var_in_kind x1 (var x) k in
      let f = subst_var_in_formula x2 (var x) f in
      kind_check env k f
  | K_ForallTerm (x1, k), F_Fix (fix, x2, f) ->
      (*  G, X : (forall y, [y < x] => K{y/x}) |- F : K  *)
      (* ----------------------------------------------- *)
      (*         G |- fix X(x). F : forall x, K          *)
      let x = fresh_var () in
      let env = map_var (map_var env x1 x) x2 x in
      let k = subst_var_in_kind x1 (var x) k in
      let f = subst_var_in_formula x2 (var x) f in
      let y = fresh_var () in
      let fix_kind = K_ForallTerm (y, K_Constr (var y <: var x, subst_var_in_kind x (var y) k)) in
      kind_check (map_fvar env fix fix_kind) k f
  | K_ForallTerm _, _ -> false
  | K_Constr (c, k), f -> kind_check (add_constr env c) k f

and kind_infer env f =
  let is_prop env f =
    match kind_infer env f with
    | Some K_Prop -> true
    | _           -> false
  in
  match f with
  | F_Var x -> find_fvar env x
  | F_Bot | F_Constr _ -> Some K_Prop
  | F_And fs | F_Or fs -> to_option K_Prop (List.for_all (is_prop env) fs)
  | F_Impl (f1, f2) -> to_option K_Prop (is_prop env f1 && is_prop env f2)
  | F_ForallTerm (_, f) | F_ForallAtom (_, f) | F_ExistsTerm (_, f) | F_ExistsAtom (_, f) ->
      to_option K_Prop (is_prop env f)
  | F_ConstrAnd (c, f) | F_ConstrImpl (c, f) -> to_option K_Prop (is_prop (add_constr env c) f)
  | F_Fun (x, k, f) -> kind_infer (map_fvar env x k) f
  | F_App (f1, f2) -> (
    match (kind_infer env f1 >>= cast_to_arrow, kind_infer env f2) with
    | Some (K_Arrow (k1, k)), Some k2 -> to_option k $ subkind env k2 k1
    | _                               -> None )
  | F_FunTerm (x, f) -> Option.map (fun k -> K_ForallTerm (x, k)) $ kind_infer env f
  | F_AppTerm (f, t) -> (
    match kind_infer env f >>= cast_to_forall_term with
    | Some (K_ForallTerm (x, k)) -> Some (subst_var_in_kind x t k)
    | _                          -> None )
  | F_FunAtom (a, f) -> Option.map (fun k -> K_ForallAtom (a, k)) $ kind_infer env f
  | F_AppAtom (f, a) -> (
    match kind_infer env f >>= cast_to_forall_atom with
    | Some (K_ForallAtom (a', k)) -> Some (subst_atom_in_kind a' a k)
    | _                           -> None )
  | F_Fix (fix, x, f) ->
      (* TODO: now we assume k is Prop, but it could be anything? *)
      let k = K_Prop in
      let y = fresh_var () in
      let fix_k = K_ForallTerm (y, K_Constr (var y <: var x, subst_var_in_kind x (var y) k)) in
      Option.map (fun k -> K_ForallTerm (x, k)) (kind_infer (map_fvar env fix fix_k) f)
