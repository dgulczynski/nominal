open Types
open KindCheckerEnv
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
    | ForallTerm (_x1, k1), ForallTerm (_x2, k2) -> subkind env k1 k2 (* TODO: add x to env*)
    | ForallAtom (_a1, k1), ForallAtom (_a2, k2) -> subkind env k1 k2 (* TODO: add a to env*)
    | _ -> false

  let check _ _ = false
end
