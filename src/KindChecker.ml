open Types
open Substitution
open KindCheckerEnv
open Common

let solve env c = mem_constr env c || Solver.solve_with_assumptions (constraints_of env) c

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
      let k1 = subst_var_in_kind x1 x k1 in
      let k2 = subst_var_in_kind x2 x k2 in
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
    | Some k' ->
        (* Technically, we should check whether k' <: k, but it is only possible for variable to be
           added to environment by kind-checking function, so by contravariance of -> we shall check
           the opposite, so whether k <: k' *)
        subkind env k k'
    | None    -> false )
  | K_Prop, F_Bot | K_Prop, F_Constr _ -> true
  | K_Prop, F_And fs | K_Prop, F_Or fs -> List.for_all (kind_check env K_Prop) fs
  | K_Prop, F_Impl (f1, f2) -> kind_check env K_Prop f1 && kind_check env K_Prop f2
  | K_Prop, F_ForallTerm (_, f)
  | K_Prop, F_ExistsTerm (_, f)
  | K_Prop, F_ForallAtom (_, f)
  | K_Prop, F_ExistsAtom (_, f) ->
      (* Is it okay to disregard quantified variable? *)
      kind_check env K_Prop f
  | K_Prop, F_ConstrImpl (c, f) | K_Prop, F_ConstrAnd (c, f) ->
      kind_check env (K_Constr (c, K_Prop)) f
  | K_Prop, _ -> false
  | K_Arrow (k1, k2), F_Fun (x, f) -> kind_check (map_fvar env x k1) k2 f
  | K_Arrow _, _ -> false
  | K_ForallAtom (a, k), F_FunAtom (a', f) when a = a' -> kind_check env k f
  | K_ForallAtom _, _ -> false
  | K_ForallTerm (x, k), F_FunTerm (x', f) when x = x' -> kind_check env k f
  | K_ForallTerm (x, k), F_Fix (fix, x', f) when x = x' ->
      (*  G, X : (forall y, [y < x] => K{y/x}) |- F : K  *)
      (* ----------------------------------------------- *)
      (*         G |- fix X(x). F : forall x, K          *)
      let y = fresh_var () in
      let fix_kind = K_ForallTerm (y, K_Constr (var y <: var x, subst_var_in_kind x y k)) in
      kind_check (map_fvar env fix fix_kind) k f
  | K_ForallTerm _, _ -> false
  | K_Constr (c, k), f -> kind_check (add_constr env c) k f
