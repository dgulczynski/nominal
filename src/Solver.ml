open Types
open SolverEnv
open Common
open Permutation

exception SolverException of string

module Solver = struct
  let fresh {perm= pi; symb= a} t = a #: (permute_term (reverse pi) t)

  let reduce env assmpts =
    let update_env env = function
      | Fresh (a, Atom {perm= []; symb= b}) | AtomNeq (a, {perm= []; symb= b}) ->
          Option.bind env (fun env -> SolverEnv.add_neq env a b)
      | constr ->
          raise
          $ SolverException
              ("Solver cannot update env with constraint " ^ Printing.string_of_constr constr)
    in
    let simple, rest =
      List.partition
        (function
          | Fresh (_, Atom {perm= []; symb= _}) | AtomNeq (_, {perm= []; symb= _}) -> true
          | _ -> false )
        assmpts
    in
    let found, assmpts' =
      find_first
        (function
          | Eq _ | AtomEq _ | AtomNeq _ | Fresh _ -> true
          | Shape _ | Subshape _ -> false )
        rest
    in
    let env' = List.fold_left update_env (Some env) simple in
    (env', assmpts', found)

  let rec solve_ env assmpts goal =
    match reduce env assmpts with
    | None, _, _                       -> true
    | Some env', assmpts', None        -> solve_by_case env' assmpts' goal
    | Some env', assmpts', Some assmpt -> solve_assmpt_by_case env' assmpts' goal assmpt

  and solve_by_case env assmpts = function
    | Eq (t1, t2)  -> solve_eq env assmpts t1 t2
    | Fresh (a, t) -> solve_fresh env assmpts a t
    | _            ->
        (* TODO: Implement solve_shape and solve_subshape *)
        false

  and solve_assmpt_by_case env assmpts goal = function
    | Eq (t1, t2)                      -> solve_assmpt_eq env assmpts goal t1 t2
    | AtomEq (a, b)                    -> solve_assmpt_eq env assmpts goal (Atom (pure a)) (Atom b)
    | Fresh (a, t)                     -> solve_assmpt_fresh env assmpts goal a t
    | AtomNeq (a, b)                   -> solve_assmpt_fresh env assmpts goal a (Atom b)
    | (Shape _ | Subshape _) as assmpt ->
        raise
        $ SolverException ("Solver doesn't know how to reduce " ^ Printing.string_of_constr assmpt)

  and solve_eq env assmpts e1 e2 =
    match (e1, e2) with
    | Atom {perm= []; symb= a}, Atom {perm; symb= b} -> (
      match outer_swap perm with
      | None            -> a = b
      | Some (swap, pi) -> solve_eq_swap env assmpts a swap $ Atom {perm= pi; symb= b} )
    | Atom {perm= pi; symb= a}, Atom b ->
        solve_eq env assmpts $ Atom (pure a) $ Atom (permute (reverse pi) b)
    | Var {perm= []; symb= x}, Var {perm= pi; symb= x'} when x = x' ->
        permutation_idempotent env assmpts pi x
    | Var {perm= pi; symb= x}, Var x' ->
        solve_eq env assmpts $ Var (pure x) $ Var (permute (reverse pi) x')
    | Lam (({perm= pi; symb= a1} as alpha1), t1), Lam (alpha2, t2) ->
        solve_fresh env assmpts a1 $ permute_term (reverse pi) e2
        && solve_eq env assmpts t1 $ permute_term [(alpha1, alpha2)] t2
    | App (t1, t2), App (t1', t2') -> solve_eq env assmpts t1 t1' && solve_eq env assmpts t2 t2'
    | Fun f, Fun f' -> f = f'
    | _ -> false

  and solve_eq_swap env assmpts a (alpha1, alpha2) e =
    solve_ env ((a =/=: alpha1) :: (a =/=: alpha2) :: assmpts) (Atom (pure a) =: e)
    && solve_ env ((a =/=: alpha1) :: (a ==: alpha2) :: assmpts) (Atom alpha1 =: e)
    && solve_ env ((a ==: alpha1) :: assmpts) (Atom alpha2 =: e)

  and permutation_idempotent env assmpts pi x =
    let test ({perm= pi; symb= a} as alpha) =
      solve_eq env assmpts (Atom alpha) (Atom (permute pi alpha))
      || solve_fresh env assmpts a $ Var {perm= reverse pi; symb= x}
    in
    List.for_all test (free_vars_of pi)

  and solve_fresh env assmpts a e =
    match e with
    | Atom {perm; symb= b} -> (
      match outer_swap perm with
      | None            -> SolverEnv.is_neq env a b
      | Some (swap, pi) -> solve_fresh_swap env assmpts a swap $ Atom {perm= pi; symb= b} )
    | Var {perm; symb= x}  -> (
      match outer_swap perm with
      | None            -> SolverEnv.is_fresh env a x
      | Some (swap, pi) -> solve_fresh_swap env assmpts a swap $ Var {perm= pi; symb= x} )
    | Lam (alpha, t)       -> solve_ env ((a =/=: alpha) :: assmpts) a #: t
    | App (t1, t2)         -> solve_fresh env assmpts a t1 && solve_fresh env assmpts a t2
    | Fun _                -> true

  and solve_fresh_swap env assmpts a (alpha1, alpha2) e =
    solve_ env ((a =/=: alpha1) :: (a =/=: alpha2) :: assmpts) $ a #: e
    && solve_ env ((a ==: alpha1) :: (a =/=: alpha2) :: assmpts) $ fresh alpha2 e
    && solve_ env ((a ==: alpha2) :: assmpts) $ fresh alpha1 e

  and solve_assmpt_fresh env assmpts goal a = function
    | Atom {perm= pi; symb= b} ->
        let swap, pi' = Option.get $ outer_swap pi in
        solve_assmpt_fresh_swap env assmpts a swap (Atom {perm= pi'; symb= b}) goal
    | Var {perm= pi; symb= x}  -> (
      match outer_swap pi with
      | None             -> solve_ (SolverEnv.add_fresh env a x) assmpts goal
      | Some (swap, pi') ->
          solve_assmpt_fresh_swap env assmpts a swap (Var {perm= pi'; symb= x}) goal )
    | Lam (alpha, t)           -> solve_ env ((a =/=: alpha) :: (a #: t) :: assmpts) goal
    | App (t1, t2)             -> solve_ env ((a #: t1) :: (a #: t2) :: assmpts) goal
    | Fun _                    -> solve_ env assmpts goal

  and solve_assmpt_fresh_swap env assmpts a (alpha1, alpha2) e goal =
    solve_ env ((a =/=: alpha1) :: (a =/=: alpha2) :: (a #: e) :: assmpts) goal
    && solve_ env ((a ==: alpha1) :: (a =/=: alpha2) :: fresh alpha2 e :: assmpts) goal
    && solve_ env ((a ==: alpha2) :: fresh alpha1 e :: assmpts) goal

  and solve_assmpt_eq env assmpts goal t1 t2 =
    match (t1, t2) with
    | Atom {perm= []; symb= a}, Atom {perm= pi; symb= b} -> (
      match outer_swap pi with
      | None             -> (
        match SolverEnv.subst_atom env a b with
        | None      -> true
        | Some env' ->
            let assmpts' = List.map (subst_atom_constr a b) assmpts in
            let goal' = subst_atom_constr a b goal in
            solve_ env' assmpts' goal' )
      | Some (swap, pi') ->
          let beta = Atom {perm= pi'; symb= b} in
          solve_assmpt_eq_swap env assmpts a swap beta goal )
    | Atom {perm= pi; symb= a}, Atom beta ->
        solve_assmpt_eq env assmpts goal $ Atom {perm= []; symb= a} $ Atom (permute pi beta)
    | Var {perm= []; symb= x}, t | t, Var {perm= []; symb= x} ->
        if occurs_check x t then false
        else
          let env' = SolverEnv.subst_var env x t in
          let assmpts' = List.map (subst_var_constr x t) assmpts in
          let goal' = subst_var_constr x t goal in
          solve_ env' assmpts' goal'
    | Var {perm= pi; symb= x}, t | t, Var {perm= pi; symb= x} ->
        solve_assmpt_eq env assmpts goal $ Var (pure x) $ permute_term pi t
    | Lam (a1, t1), Lam (a2, t2) ->
        solve_ env (fresh a1 (Lam (a2, t2)) :: (t1 =: permute_term [(a1, a2)] t2) :: assmpts) goal
    | App (t1, t2), App (t1', t2') -> solve_ env ((t1 =: t2) :: (t1' =: t2') :: assmpts) goal
    | Fun f, Fun f' -> f != f' || solve_ env assmpts goal
    | t1, t2 ->
        raise
        $ SolverException
            ("Unimplemented " ^ Printing.string_of_term t1 ^ " =: " ^ Printing.string_of_term t2)

  and solve_assmpt_eq_swap env assmpts a (alpha1, alpha2) e goal =
    solve_ env ((Atom (pure a) =: e) :: (a =/=: alpha1) :: (a =/=: alpha2) :: assmpts) goal
    && solve_ env ((Atom alpha2 =: e) :: (a ==: alpha1) :: assmpts) goal
    && solve_ env ((Atom alpha1 =: e) :: (a =/=: alpha1) :: (a ==: alpha2) :: assmpts) goal

  let solve_with_env env = solve_ env []

  let solve = solve_with_env SolverEnv.empty

  let solve_with_assumptions = solve_ SolverEnv.empty
end
