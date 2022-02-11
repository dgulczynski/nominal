open Types
open Common
open Permutation
open Substitution

exception SolverException of string

let fresh {perm= pi; symb= a} t = a #: (permute_term (reverse pi) t)

let reduce env assmpts =
  let update_env env = function
    | C_Fresh (a, T_Atom {perm= []; symb= b}) | C_AtomNeq (a, {perm= []; symb= b}) ->
        Option.bind env (fun env -> SolverEnv.add_neq env a b)
    | C_Fresh (a, T_Var {perm= []; symb= x}) ->
        Option.map (fun env -> SolverEnv.add_fresh env a x) env
    | _ ->
        (* This cannot happen as only "simple" constraints should be chosen for updating env *)
        assert false
  in
  let simple, rest =
    List.partition
      (function
        | C_Fresh (_, T_Atom {perm= []; _}) | C_AtomNeq (_, {perm= []; _}) -> true
        | C_Fresh (_, T_Var {perm= []; _}) -> true
        | _ -> false )
      assmpts
  in
  let found, assmpts =
    find_first
      (function
        | C_Eq _ | C_AtomEq _ | C_AtomNeq _ | C_Fresh _ -> true
        | C_Shape _ | C_Subshape _ -> false )
      rest
  in
  let env = List.fold_left update_env (Some env) simple in
  (env, assmpts, found)

let rec solve_ env assmpts goal =
  match reduce env assmpts with
  | None, _, _                     -> true
  | Some env, assmpts, None        -> solve_by_case env assmpts goal
  | Some env, assmpts, Some assmpt -> solve_assmpt_by_case env assmpts goal assmpt

and solve_by_case env assmpts = function
  | C_Eq (t1, t2)        -> solve_eq env assmpts t1 t2
  | C_AtomEq (a, alpha)  -> solve_eq env assmpts (T_Atom (pure a)) (T_Atom alpha)
  | C_Fresh (a, t)       -> solve_fresh env assmpts a t
  | C_AtomNeq (a, alpha) -> solve_fresh env assmpts a (T_Atom alpha)
  | C_Shape (t1, t2)     -> solve_shape env assmpts t1 t2
  | C_Subshape (t1, t2)  -> solve_subshape env assmpts t1 t2

and solve_assmpt_by_case env assmpts goal = function
  | C_Eq (t1, t2) -> solve_assmpt_eq env assmpts goal t1 t2
  | C_AtomEq (a, b) -> solve_assmpt_eq env assmpts goal (T_Atom (pure a)) (T_Atom b)
  | C_Fresh (a, t) -> solve_assmpt_fresh env assmpts goal a t
  | C_AtomNeq (a, b) -> solve_assmpt_fresh env assmpts goal a (T_Atom b)
  | (C_Shape _ | C_Subshape _) as assmpt ->
      (* TODO: implement solve_assmpt_shape and solve_assmpt_subshape *)
      raise $ SolverException ("Solver isn't yet able to reduce " ^ Printing.string_of_constr assmpt)

and solve_eq env assmpts e1 e2 =
  match (e1, e2) with
  | T_Atom {perm= []; symb= a}, T_Atom {perm; symb= b} -> (
    match outer_swap perm with
    | None            -> a = b
    | Some (swap, pi) ->
        solve_swap_cases env a swap (const assmpts) (fun a ->
            T_Atom a =: T_Atom {perm= pi; symb= b} ) )
  | T_Atom {perm= pi; symb= a}, T_Atom b ->
      solve_eq env assmpts $ T_Atom (pure a) $ T_Atom (permute (reverse pi) b)
  | T_Atom _, _ -> false
  | T_Var {perm= []; symb= x}, T_Var {perm= pi; symb= x'} when x = x' ->
      permutation_idempotent env assmpts pi x
  | T_Var {perm= pi; symb= x}, T_Var x' ->
      solve_eq env assmpts $ var x $ T_Var (permute (reverse pi) x')
  | T_Var _, _ -> false
  | T_Lam (({perm= pi; symb= a1} as alpha1), t1), T_Lam (alpha2, t2) ->
      solve_fresh env assmpts a1 $ permute_term (reverse pi) e2
      && solve_eq env assmpts t1 $ permute_term [(alpha1, alpha2)] t2
  | T_Lam _, _ -> false
  | T_App (t1, t2), T_App (t1', t2') -> solve_eq env assmpts t1 t1' && solve_eq env assmpts t2 t2'
  | T_App _, _ -> false
  | T_Fun f, T_Fun f' -> f = f'
  | T_Fun _, _ -> false

and permutation_idempotent env assmpts pi x =
  let test ({perm= pi; symb= a} as alpha) =
    solve_eq env assmpts (T_Atom alpha) (T_Atom (permute pi alpha))
    || solve_fresh env assmpts a $ T_Var {perm= reverse pi; symb= x}
  in
  List.for_all test (free_vars_of pi)

and solve_fresh env assmpts a e =
  match e with
  | T_Atom {perm; symb= b} -> (
    match outer_swap perm with
    | None            -> SolverEnv.is_neq env a b
    | Some (swap, pi) -> solve_fresh_swap env assmpts a swap $ T_Atom {perm= pi; symb= b} )
  | T_Var {perm; symb= x}  -> (
    match outer_swap perm with
    | None            -> SolverEnv.is_fresh env a x
    | Some (swap, pi) -> solve_fresh_swap env assmpts a swap $ T_Var {perm= pi; symb= x} )
  | T_Lam (alpha, t)       -> solve_ env ((a =/=: alpha) :: assmpts) a #: t
  | T_App (t1, t2)         -> solve_fresh env assmpts a t1 && solve_fresh env assmpts a t2
  | T_Fun _                -> true

and solve_fresh_swap env assmpts a (alpha1, alpha2) e =
  solve_ env ((a =/=: alpha1) :: (a =/=: alpha2) :: assmpts) $ a #: e
  && solve_ env ((a ==: alpha1) :: (a =/=: alpha2) :: assmpts) $ fresh alpha2 e
  && solve_ env ((a ==: alpha2) :: assmpts) $ fresh alpha1 e

(* TODO: Implement solve_shape and solve_subshape *)
and solve_shape _ _ _ _ = false

and solve_subshape _ _ _ _ = false

and solve_assmpt_fresh env assmpts goal a = function
  | T_Atom {perm= pi; symb= b} ->
      (* Here we use Option.get because we are sure that the permutation is non-empty, because if it
         was, it would already be merged into the env by the reduce function *)
      let swap, pi = Option.get $ outer_swap pi in
      solve_swap_cases env a swap
        (fun a -> fresh a (T_Atom {perm= pi; symb= b}) :: assmpts)
        (const goal)
  | T_Var {perm= pi; symb= x}  ->
      (* See comment above: we are sure the permutation is non-empty here *)
      let swap, pi = Option.get $ outer_swap pi in
      solve_swap_cases env a swap
        (fun a -> fresh a (T_Var {perm= pi; symb= x}) :: assmpts)
        (const goal)
  | T_Lam (alpha, t)           ->
      solve_ env ((a ==: alpha) :: assmpts) goal
      && solve_ env ((a =/=: alpha) :: (a #: t) :: assmpts) goal
  | T_App (t1, t2)             -> solve_ env ((a #: t1) :: (a #: t2) :: assmpts) goal
  | T_Fun _                    -> solve_ env assmpts goal

and solve_assmpt_eq env assmpts goal t1 t2 =
  match (t1, t2) with
  | T_Atom {perm= []; symb= a}, T_Atom {perm= pi; symb= b} -> (
    match outer_swap pi with
    | None            -> (
      match SolverEnv.subst_atom env a b with
      | None     -> true
      | Some env ->
          let assmpts = List.map (subst_atom_in_constr a b) assmpts in
          let goal = subst_atom_in_constr a b goal in
          solve_ env assmpts goal )
    | Some (swap, pi) ->
        solve_swap_cases env a swap
          (fun a -> (T_Atom a =: T_Atom {perm= pi; symb= b}) :: assmpts)
          (const goal) )
  | T_Atom {perm= pi; symb= a}, T_Atom beta ->
      solve_assmpt_eq env assmpts goal $ T_Atom {perm= []; symb= a} $ T_Atom (permute pi beta)
  | T_Atom _, _ -> true
  | T_Var {perm= []; symb= x}, T_Var {perm= []; symb= x'} when x = x' -> solve_ env assmpts goal
  | T_Var {perm= []; symb= x}, t | t, T_Var {perm= []; symb= x} ->
      if occurs_check x t then true
      else
        let env, env_assmpts = SolverEnv.subst_var env x t in
        let assmpts = List.map (subst_var_in_constr x t) assmpts in
        let goal = subst_var_in_constr x t goal in
        solve_ env (env_assmpts @ assmpts) goal
  | T_Var {perm= pi; symb= x}, t | t, T_Var {perm= pi; symb= x} ->
      solve_assmpt_eq env assmpts goal $ var x $ permute_term pi t
  | T_Lam (a1, t1), T_Lam (a2, t2) ->
      solve_ env (fresh a1 (T_Lam (a2, t2)) :: (t1 =: permute_term [(a1, a2)] t2) :: assmpts) goal
  | T_Lam _, _ -> true
  | T_App (t1, t2), T_App (t1', t2') -> solve_ env ((t1 =: t2) :: (t1' =: t2') :: assmpts) goal
  | T_App _, _ -> true
  | T_Fun f, T_Fun f' -> f != f' || solve_ env assmpts goal
  | T_Fun _, _ -> true

and solve_swap_cases env a (alpha1, alpha2) assmpt_gen goal_gen =
  solve_ env ((a =/=: alpha1) :: (a =/=: alpha2) :: assmpt_gen (pure a)) (goal_gen (pure a))
  && solve_ env ((a ==: alpha1) :: (a =/=: alpha2) :: assmpt_gen alpha2) (goal_gen alpha2)
  && solve_ env ((a ==: alpha2) :: assmpt_gen alpha1) (goal_gen alpha1)

let solve_with_env env = solve_ env []

let solve = solve_with_env SolverEnv.empty

let solve_with_assumptions = solve_ SolverEnv.empty
