open Types
open SolverEnv
open Common
open Permutation

module Solver = struct
  let rec solve_fresh env a e =
    match e with
    | Atom (Just b) -> SolverEnv.is_neq env a b
    | Var (Just x) -> SolverEnv.is_fresh env a x
    | Lam (Just b, _) when a = b -> true
    | Lam (Just b, t) -> (
      match SolverEnv.add_neq env a b with
      | None      -> true
      | Some env' -> solve_fresh env' a t )
    | App (t1, t2) -> solve_fresh env a t1 && solve_fresh env a t2
    | Fun _ -> true
    | _ -> false

  let rec solve_eq env e1 e2 =
    match (e1, e2) with
    | Atom (Just a), Atom (Just a') -> a = a'
    | Atom (Permuted (pi, a)), Atom b ->
        solve_eq env $ Atom (Just a) $ Atom (permute pi b)
    | Atom (Just a), Atom (Permuted (_, b)) ->
        (* TODO *) solve_eq env $ Atom (Just a) $ Atom (Just b)
    | Var (Just x), Var (Just x') -> x = x'
    | Var (Permuted (pi, x)), Var y -> solve_eq env $ Var (Just x) $ Var (permute pi y)
    | Var (Just x), Var (Permuted (_, y)) ->
        (* TODO *) solve_eq env $ Var (Just x) $ Var (Just y)
    | Lam ((Just a1 as alpha1), t1), Lam (alpha2, t2) ->
        solve_fresh env a1 e2 && solve_eq env t1 $ permute_term [(alpha1, alpha2)] t2
    | Lam ((Permuted (pi, a1) as alpha1), t1), Lam (alpha2, t2) ->
        solve_fresh env a1 $ permute_term (reverse pi) e2
        && solve_eq env t1 $ permute_term [(alpha1, alpha2)] t2
    | App (t1, t2), App (t1', t2') -> solve_eq env t1 t1' && solve_eq env t2 t2'
    | Fun f, Fun f' -> f = f'
    | _ -> false

  let solve_with_env env = function
    | Eq (t1, t2)  -> solve_eq env t1 t2
    | Fresh (a, t) -> solve_fresh env a t
    | _            -> false

  let solve = solve_with_env SolverEnv.empty
end
