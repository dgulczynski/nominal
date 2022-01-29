open Types
open KindCheckerEnv
open Solver
open Substitution

module KindChecker = struct
  let solve env c =
    KindCheckerEnv.mem_constr env c
    || Solver.solve_with_assumptions (KindCheckerEnv.constraints_of env) c

  let rec subkind env k1 k2 =
    match (k1, k2) with
    | K_Prop, K_Prop -> true
    | K_Prop, _ -> false
    | K_Arrow (k1, k1'), K_Arrow (k2, k2') -> subkind env k2 k1 && subkind env k1' k2'
    | K_Arrow _, _ -> false
    | k1, K_Constr (c, k2) -> subkind (KindCheckerEnv.add_constr env c) k1 k2
    | K_Constr (c, k1), k2 -> solve env c && subkind env k1 k2
    | K_ForallTerm (x1, k1), K_ForallTerm (x2, k2) ->
        let x = fresh_var () in
        let env' = KindCheckerEnv.map_var (KindCheckerEnv.map_var env x1 x) x2 x in
        let k1' = subst_var_in_kind x1 x k1 in
        let k2' = subst_var_in_kind x2 x k2 in
        subkind env' k1' k2'
    | K_ForallTerm _, _ -> false
    | K_ForallAtom (a1, k1), K_ForallAtom (a2, k2) ->
        let a = fresh_atom () in
        let env' = KindCheckerEnv.map_atom (KindCheckerEnv.map_atom env a1 a) a2 a in
        let k1' = subst_atom_in_kind a1 a k1 in
        let k2' = subst_atom_in_kind a2 a k2 in
        subkind env' k1' k2'
    | K_ForallAtom _, _ -> false

  let check _ _ = false
end
