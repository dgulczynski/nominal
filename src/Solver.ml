open Types
open SolverEnv
open Common
open Permutation

module Solver = struct
  let rec solve_fresh env assmpts a e =
    match e with
    | Atom {perm= []; symb= b} -> SolverEnv.is_neq env a b
    | Atom {perm= (alpha1, alpha2) :: pi; symb= b} ->
        (* TODO: add assumptions to env *)
        (* TODO: convert to cps *)
        solve_fresh env assmpts a $ Atom {perm= pi; symb= b}
        && solve_fresh env assmpts a $ Atom (permute pi alpha2)
        && solve_fresh env assmpts a $ Atom (permute pi alpha1)
    | Var {perm= []; symb= x} -> SolverEnv.is_fresh env a x
    | Var {perm= (_alpha1, _alpha2) :: pi; symb= x} ->
        (* TODO: add assumptions to env *)
        solve_fresh env assmpts a $ Var {perm= pi; symb= x}
    | Lam ({perm= []; symb= b}, _) when a = b -> true
    | Lam (alpha, t) ->
        let assmpts' = AtomNeq (a, alpha) :: assmpts in
        _solve env assmpts' $ Fresh (a, t)
    | App (t1, t2) -> solve_fresh env assmpts a t1 && solve_fresh env assmpts a t2
    | Fun _ -> true

  and solve_eq env assmpts e1 e2 =
    (* TODO: improve readability *)
    match (e1, e2) with
    | Atom {perm= []; symb= a}, Atom {perm= []; symb= a'} -> a = a'
    | Atom {perm= []; symb= a}, Atom {perm= _pi; symb= b} ->
        (* TODO: add assumptions to env *)
        solve_eq env assmpts $ Atom {perm= []; symb= a} $ Atom {perm= []; symb= b}
    | Atom {perm= pi; symb= a}, Atom b ->
        solve_eq env assmpts $ Atom {perm= []; symb= a} $ Atom (permute pi b)
    | Var {perm= []; symb= x}, Var {perm= []; symb= x'} -> x = x'
    | Var {perm= []; symb= x}, Var {perm= pi; symb= x'} when x = x' ->
        (* TODO: convert to cps *)
        let test ({perm= pi; symb= a} as alpha) =
          solve_eq env assmpts (Atom alpha) (Atom (permute pi alpha))
          || solve_fresh env assmpts a $ Var {perm= reverse pi; symb= x}
        in
        List.for_all test $ free_vars_of pi
    | Var {perm= pi; symb= x}, Var x' ->
        solve_eq env assmpts $ Var {perm= []; symb= x} $ Var (permute pi x')
    | Lam (({perm= pi; symb= a1} as alpha1), t1), Lam (alpha2, t2) ->
        (* TODO: convert to cps *)
        solve_fresh env assmpts a1 $ permute_term (reverse pi) e2
        && solve_eq env assmpts t1 $ permute_term [(alpha1, alpha2)] t2
    | App (t1, t2), App (t1', t2') ->
        solve_eq env assmpts t1 t1' && solve_eq env assmpts t2 t2'
    | Fun f, Fun f' -> f = f'
    | _ -> false

  and _solve env assmpts = function
    | Eq (t1, t2)  -> solve_eq env assmpts t1 t2
    | Fresh (a, t) -> solve_fresh env assmpts a t
    | _            -> false

  let solve_with_env env = _solve env []

  let solve = solve_with_env SolverEnv.empty
end
