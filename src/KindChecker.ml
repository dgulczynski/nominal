open Types
open KindCheckerEnv
open Common
open Solver

module KindChecker = struct
  let solve env c =
    KindCheckerEnv.mem_constr env c
    || Solver.solve_with_assumptions (KindCheckerEnv.constraints_of env) c

  let rec subkind env k1 k2 =
    match (k1, k2) with
    | Prop, Prop -> true
    | Arrow (k1, k1'), Arrow (k2, k2') -> subkind env k2 k1 && subkind env k1' k2'
    | k1, Constr (c, k2) -> subkind (KindCheckerEnv.add_constr env c) k1 k2
    | Constr (c, k1), k2 -> solve env c && subkind env k1 k2
    | ForallTerm (x1, k1), ForallTerm (x2, k2) ->
        let x = fresh_var () in
        let env' = KindCheckerEnv.map_var (KindCheckerEnv.map_var env x1 x) x2 x in
        let k1' = subst_var_kind x1 x k1 in
        let k2' = subst_var_kind x2 x k2 in
        subkind env' k1' k2'
    | ForallAtom (a1, k1), ForallAtom (a2, k2) ->
        let a = fresh_atom () in
        let env' = KindCheckerEnv.map_atom (KindCheckerEnv.map_atom env a1 a) a2 a in
        let k1' = subst_atom_kind a1 a k1 in
        let k2' = subst_atom_kind a2 a k2 in
        subkind env' k1' k2'
    | _ -> false

  let check _ _ = false
end
