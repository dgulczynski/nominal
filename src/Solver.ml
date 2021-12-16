open Types
open SolverEnv
open Common
open Permutation

module Solver = struct
  let reduce env assmpts =
    let simple, rest =
      List.partition
        (function
          | Fresh (_, Atom {perm= []; symb= _}) | AtomNeq (_, {perm= []; symb= _}) -> true
          | _ -> false )
        assmpts
    in
    let update_env env = function
      | Fresh (a, Atom {perm= []; symb= b}) | AtomNeq (a, {perm= []; symb= b}) ->
          Option.bind env (fun env -> SolverEnv.add_neq env a b)
      | _ -> env
    in
    let found, assmpts' =
      find_first
        (function AtomEq _ | AtomNeq _ | Fresh (_, Atom _) -> true | _ -> false)
        rest
    in
    let env' = List.fold_left update_env (Some env) simple in
    (env', assmpts', found)

  let rec solve_fresh env assmpts a e =
    match e with
    | Atom {perm; symb= b} -> (
      match inner_swap perm with
      | None                        -> SolverEnv.is_neq env a b
      | Some ((alpha1, alpha2), pi) ->
          (* TODO: convert to cps *)
          solve_ env (AtomNeq (b, alpha1) :: AtomNeq (b, alpha2) :: assmpts)
          $ Fresh (a, Atom {perm= pi; symb= b})
          && solve_ env (AtomEq (b, alpha1) :: assmpts)
             $ Fresh (a, Atom (permute pi alpha2))
          && solve_ env (AtomEq (b, alpha2) :: assmpts)
             $ Fresh (a, Atom (permute pi alpha1)) )
    | Var {perm; symb= x}  -> (
      match outer_swap perm with
      | None                        -> SolverEnv.is_fresh env a x
      | Some ((alpha1, alpha2), pi) ->
          let c = Fresh (a, Var {perm= pi; symb= x}) in
          (* TODO: convert to cps *)
          solve_ env (AtomNeq (a, alpha1) :: AtomNeq (a, alpha2) :: assmpts) c
          && solve_ env (AtomNeq (a, alpha1) :: AtomEq (a, alpha2) :: assmpts) c
          && solve_ env (AtomEq (a, alpha1) :: assmpts) c )
    | Lam (alpha, t)       -> solve_ env (AtomNeq (a, alpha) :: assmpts) $ Fresh (a, t)
    | App (t1, t2)         -> solve_fresh env assmpts a t1 && solve_fresh env assmpts a t2
    | Fun _                -> true

  and solve_eq env assmpts e1 e2 =
    match (e1, e2) with
    | Atom {perm= []; symb= a}, Atom {perm; symb= b} -> (
      match outer_swap perm with
      | None                        -> a = b
      | Some ((alpha1, alpha2), pi) ->
          let b' = Atom {perm= pi; symb= b} in
          (* TODO: convert to cps *)
          solve_ env (AtomNeq (a, alpha1) :: AtomNeq (a, alpha2) :: assmpts) $ Eq (e1, b')
          && solve_ env (AtomNeq (a, alpha1) :: AtomEq (a, alpha2) :: assmpts)
             $ Eq (Atom alpha1, b')
          && solve_ env (AtomEq (a, alpha1) :: assmpts) $ Eq (Atom alpha2, b') )
    | Atom {perm= pi; symb= a}, Atom b ->
        solve_eq env assmpts $ Atom (pure a) $ Atom (permute (reverse pi) b)
    | Var {perm= []; symb= x}, Var {perm= pi; symb= x'} ->
        (* TODO: convert to cps *)
        let test ({perm= pi; symb= a} as alpha) =
          solve_eq env assmpts (Atom alpha) (Atom (permute pi alpha))
          || solve_fresh env assmpts a $ Var {perm= reverse pi; symb= x}
        in
        x = x' && List.for_all test $ free_vars_of pi
    | Var {perm= pi; symb= x}, Var x' ->
        solve_eq env assmpts $ Var (pure x) $ Var (permute (reverse pi) x')
    | Lam (({perm= pi; symb= a1} as alpha1), t1), Lam (alpha2, t2) ->
        (* TODO: convert to cps *)
        solve_fresh env assmpts a1 $ permute_term (reverse pi) e2
        && solve_eq env assmpts t1 $ permute_term [(alpha1, alpha2)] t2
    | App (t1, t2), App (t1', t2') ->
        solve_eq env assmpts t1 t1' && solve_eq env assmpts t2 t2'
    | Fun f, Fun f' -> f = f'
    | _ -> false

  and solve_ env assmpts c =
    match reduce env assmpts with
    | None, _, _                  -> true
    | Some env', assmpts', assmpt ->
    match assmpt with
    | Some (Fresh (a, Atom {perm= pi; symb= b})) | Some (AtomNeq (a, {perm= pi; symb= b}))
      ->
        let (alpha1, alpha2), pi' = Option.get $ outer_swap pi in
        (* TODO: convert to cps *)
        solve_ env'
          ( AtomNeq (a, alpha1)
          :: AtomNeq (a, alpha2)
          :: AtomNeq (a, {perm= pi'; symb= b})
          :: assmpts' )
          c
        && solve_ env'
             ( AtomEq (b, alpha1)
             :: AtomNeq (b, alpha2)
             :: AtomNeq (a, permute pi' alpha2)
             :: assmpts' )
             c
        && solve_ env'
             (AtomEq (b, alpha2) :: AtomNeq (a, permute pi' alpha1) :: assmpts')
             c
    | Some (AtomEq (a, {perm= []; symb= b})) ->
        let senv = SolverEnv.subst_atom env' a b in
        let sassmpts = List.map (subst_atom_constr a b) assmpts' in
        let sc = subst_atom_constr a b c in
        solve_ senv sassmpts sc
    | _ ->
    match c with
    | Eq (t1, t2)  -> solve_eq env' assmpts' t1 t2
    | Fresh (a, t) -> solve_fresh env' assmpts' a t
    | _            -> false

  let solve_with_env env = solve_ env []

  let solve = solve_with_env SolverEnv.empty
end
