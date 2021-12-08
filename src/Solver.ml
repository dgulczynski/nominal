open Types
open SolverEnv

module Solver = struct
  let rec solve_fresh env a e =
    match e with
    | Atom (Just b) -> SolverEnv.is_neq env a b
    | Var (Just x) -> SolverEnv.is_fresh env a x
    | Lam (Just b, _) when a = b -> true
    | Lam (Just b, t) -> (
      match SolverEnv.add_neq env a b with
      | None      -> false
      | Some env' -> solve_fresh env' a t )
    | App (t1, t2) -> solve_fresh env a t1 && solve_fresh env a t2
    | Fun _ -> true
    | _ -> false

  let rec solve_eq env e1 e2 =
    match (e1, e2) with
    | Atom (Just a), Atom (Just b) -> a = b
    | Var (Just x), Var (Just y) -> x = y
    | Lam (Just a1, t1), Lam (_, t2) -> solve_fresh env a1 e2 && solve_eq env t1 t2
    | App (t1, t2), App (t1', t2') -> solve_eq env t1 t1' && solve_eq env t2 t2'
    | Fun f, Fun g -> f = g
    | _ -> false

  let solve_with_env env = function
    | Eq (t1, t2)  -> solve_eq env t1 t2
    | Fresh (a, t) -> solve_fresh env a t
    | _            -> false

  let solve = solve_with_env SolverEnv.empty
end
