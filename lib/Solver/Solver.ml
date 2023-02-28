open Types
open Common
open Permutation
open Substitution

let fresh {perm= pi; symb= a} t = a #: (permute_term (reverse pi) t)

let reduce env assms =
  let update_env env = function
    | C_Fresh (a, T_Atom {perm= []; symb= b}) | C_AtomNeq (a, {perm= []; symb= b}) ->
        env >>= fun env -> SolverEnv.add_neq env a b
    | C_Fresh (a, T_Var {perm= []; symb= x}) -> (fun env -> SolverEnv.add_fresh env a x) <$> env
    | _ ->
        (* This cannot happen as only "simple" constraints should be chosen for updating env *)
        assert false
  in
  let simple, assms =
    List.partition
      (function
        | C_Fresh (_, T_Atom {perm= []; _}) | C_AtomNeq (_, {perm= []; _}) -> true
        | C_Fresh (_, T_Var {perm= []; _}) -> true
        | _ -> false )
      assms
  in
  let env = List.fold_left update_env (Some env) simple in
  (env, assms)

let rec solve_ env assms goal =
  match reduce env assms with
  | None, _                 -> true
  | Some env, []            -> solve_by_case env [] goal
  | Some env, assm :: assms -> solve_assm_by_case env assms goal assm

and solve_by_case env assms = function
  | C_Eq (t1, t2)        -> solve_eq env assms t1 t2
  | C_AtomEq (a, alpha)  -> solve_eq env assms (T_Atom (pure a)) (T_Atom alpha)
  | C_Fresh (a, t)       -> solve_fresh env assms a t
  | C_AtomNeq (a, alpha) -> solve_fresh env assms a (T_Atom alpha)
  | C_Shape (t1, t2)     -> solve_shape env assms t1 t2
  | C_Subshape (t1, t2)  -> solve_subshape env assms t1 t2

and solve_assm_by_case env assms goal = function
  | C_Eq (t1, t2)       -> solve_assm_eq env assms goal t1 t2
  | C_AtomEq (a, b)     -> solve_assm_eq env assms goal (T_Atom (pure a)) (T_Atom b)
  | C_Fresh (a, t)      -> solve_assm_fresh env assms goal a t
  | C_AtomNeq (a, b)    -> solve_assm_fresh env assms goal a (T_Atom b)
  | C_Shape (t1, t2)    -> solve_assm_shape env assms goal t1 t2
  | C_Subshape (t1, t2) -> solve_assm_subshape env assms goal t1 t2

and solve_eq env assms e1 e2 =
  match (e1, e2) with
  | T_Atom {perm= []; symb= a}, T_Atom {perm; symb= b} -> (
    match outer_swap perm with
    | None            -> a = b
    | Some (swap, pi) ->
        solve_swap_cases env a swap (const assms) (fun a -> T_Atom a =: T_Atom {perm= pi; symb= b})
    )
  | T_Atom {perm= pi; symb= a}, T_Atom b ->
      solve_eq env assms $ T_Atom (pure a) $ T_Atom (permute (reverse pi) b)
  | T_Atom _, _ -> false
  | T_Var {perm= []; symb= x}, T_Var {perm= pi; symb= x'} when x = x' ->
      permutation_idempotent env assms pi x
  | T_Var {perm= pi; symb= x}, T_Var {symb= x'; _} when x = x' ->
      solve_eq env assms $ var x $ permute_term (reverse pi) e2
  | T_Var _, _ -> false
  | T_Lam (({perm= pi; symb= a1} as alpha1), t1), T_Lam (alpha2, t2) ->
      solve_fresh env assms a1 $ permute_term (reverse pi) e2
      && solve_eq env assms t1 $ permute_term [(alpha1, alpha2)] t2
  | T_Lam _, _ -> false
  | T_App (t1, t2), T_App (t1', t2') -> solve_eq env assms t1 t1' && solve_eq env assms t2 t2'
  | T_App _, _ -> false
  | T_Fun f1, T_Fun f2 -> f1 = f2
  | T_Fun _, _ -> false

and permutation_idempotent env assms pi x =
  let test ({perm= pi; symb= a} as alpha) =
    solve_eq env assms (T_Atom alpha) (T_Atom (permute pi alpha))
    || solve_fresh env assms a $ T_Var {perm= reverse pi; symb= x}
  in
  List.for_all test (free_vars_of pi)

and solve_fresh env assms a e =
  let solve_fresh_swap swap t = solve_swap_cases env a swap (const assms) (flip fresh t) in
  match e with
  | T_Atom {perm; symb= b} -> (
    match outer_swap perm with
    | None            -> SolverEnv.is_neq env a b
    | Some (swap, pi) -> solve_fresh_swap swap $ T_Atom {perm= pi; symb= b} )
  | T_Var {perm; symb= x}  -> (
    match outer_swap perm with
    | None            -> SolverEnv.is_fresh env a x
    | Some (swap, pi) -> solve_fresh_swap swap $ T_Var {perm= pi; symb= x} )
  | T_Lam (alpha, t)       -> solve_ env ((a =/=: alpha) :: assms) a #: t
  | T_App (t1, t2)         -> solve_fresh env assms a t1 && solve_fresh env assms a t2
  | T_Fun _                -> true

and solve_shape env assms t1 t2 =
  match (t1, t2) with
  | T_Var {symb= x1; _}, T_Var {symb= x2; _} -> SolverEnv.are_same_shape env x1 x2
  | T_Var _, _ -> false
  | T_Atom _, T_Atom _ -> true
  | T_Atom _, _ -> false
  | T_Lam (_, t1), T_Lam (_, t2) -> solve_shape env assms t1 t2
  | T_Lam _, _ -> false
  | T_App (t1, t1'), T_App (t2, t2') -> solve_shape env assms t1 t2 && solve_shape env assms t1' t2'
  | T_App _, _ -> false
  | T_Fun f1, T_Fun f2 -> f1 = f2
  | T_Fun _, _ -> false

and solve_subshape env assms t1 = function
  | T_Var {symb= x; _} ->
      (*   (t2 < x) ∈ G          (t2 < x) ∈ G   *)
      (*   G |- t1 ~ t2          G |- t1 < t2   *)
      (* ----------------      ---------------- *)
      (*   G |- t1 < x           G |- t1 < x    *)
      List.exists (solve_shape_or_subshape env assms t1) $ SolverEnv.get_subshapes env x
  | T_Lam (_, t2)      ->
      (*   G |- t1 ~ t2          G |- t1 < t2   *)
      (* ----------------      ---------------- *)
      (*  G |- t1 < _.t2        G |- t1 < _.t2  *)
      solve_shape_or_subshape env assms t1 t2
  | T_App (t2, t2')    ->
      (*   G |- t1 ~ t2         G |- t1 < t2          G |- t1 ~ t2'         G |- t1 < t2'    *)
      (* ------------------   ------------------   -------------------   ------------------- *)
      (*  G |- t1 < t2 t2'     G |- t1 < t2 t2'      G |- t1 < t2 t2'      G |- t1 < t2 t2'  *)
      solve_shape_or_subshape env assms t1 t2 || solve_shape_or_subshape env assms t1 t2'
  | T_Atom _ | T_Fun _ -> false

and solve_shape_or_subshape env assms t1 t2 =
  solve_shape env assms t1 t2 || solve_subshape env assms t1 t2

and solve_assm_fresh env assms goal a = function
  | T_Atom {perm= pi; symb= b} ->
      (* Here we use Option.get because we are sure that the permutation is non-empty, because if it
         was, it would already be merged into the env by the reduce function *)
      let swap, pi = Option.get $ outer_swap pi in
      solve_swap_cases env a swap
        (fun a -> fresh a (T_Atom {perm= pi; symb= b}) :: assms)
        (const goal)
  | T_Var {perm= pi; symb= x}  ->
      (* See comment above: we are sure the permutation is non-empty here *)
      let swap, pi = Option.get $ outer_swap pi in
      solve_swap_cases env a swap
        (fun a -> fresh a (T_Var {perm= pi; symb= x}) :: assms)
        (const goal)
  | T_Lam (alpha, t)           ->
      solve_ env ((a ==: alpha) :: assms) goal
      && solve_ env ((a =/=: alpha) :: (a #: t) :: assms) goal
  | T_App (t1, t2)             -> solve_ env ((a #: t1) :: (a #: t2) :: assms) goal
  | T_Fun _                    -> solve_ env assms goal

and solve_assm_eq env assms goal t1 t2 =
  match (t1, t2) with
  | T_Atom {perm= []; symb= a}, T_Atom {perm= pi; symb= b} -> (
    match outer_swap pi with
    | None            -> (
      match SolverEnv.subst_atom env a b with
      | None     -> true
      | Some env ->
          let assms = List.map (subst_atom_in_constr a b) assms in
          let goal = subst_atom_in_constr a b goal in
          solve_ env assms goal )
    | Some (swap, pi) ->
        solve_swap_cases env a swap
          (fun a -> (T_Atom a =: T_Atom {perm= pi; symb= b}) :: assms)
          (const goal) )
  | T_Atom {perm= pi; symb= a}, T_Atom beta ->
      solve_assm_eq env assms goal $ T_Atom {perm= []; symb= a} $ T_Atom (permute pi beta)
  | T_Atom _, _ -> true
  | T_Var {perm= []; symb= x}, T_Var {perm= []; symb= x'} when x = x' -> solve_ env assms goal
  | T_Var {perm= []; symb= x}, t | t, T_Var {perm= []; symb= x} ->
      solve_assm_subst_var env assms goal x t
  | T_Var {perm= pi; symb= x}, t | t, T_Var {perm= pi; symb= x} ->
      solve_assm_eq env assms goal $ var x $ permute_term pi t
  | T_Lam (a1, t1), T_Lam (a2, t2) ->
      solve_ env (fresh a1 (T_Lam (a2, t2)) :: (t1 =: permute_term [(a1, a2)] t2) :: assms) goal
  | T_Lam _, _ -> true
  | T_App (t1, t2), T_App (t1', t2') -> solve_ env ((t1 =: t1') :: (t2 =: t2') :: assms) goal
  | T_App _, _ -> true
  | T_Fun f, T_Fun f' -> f <> f' || solve_ env assms goal
  | T_Fun _, _ -> true

and solve_swap_cases env a (alpha1, alpha2) assm_gen goal_gen =
  solve_ env ((a =/=: alpha1) :: (a =/=: alpha2) :: assm_gen (pure a)) (goal_gen (pure a))
  && solve_ env ((a ==: alpha1) :: (a =/=: alpha2) :: assm_gen alpha2) (goal_gen alpha2)
  && solve_ env ((a ==: alpha2) :: assm_gen alpha1) (goal_gen alpha1)

and solve_assm_shape env assms goal t1 t2 =
  match (t1, t2) with
  | T_Var {symb= x1; _}, T_Var {symb= x2; _} -> (
    match SolverEnv.add_same_shape env x1 x2 with
    | None     -> true
    | Some env -> solve_ env assms goal )
  | T_Var {symb= x; _}, t -> (
      (* Is this sound? Does it ever stop? Maybe not *)
      (* vs is the mapping from fresh variables to variables of original term t *)
      let t, vs = term_of_shape (shape_of_term t) in
      match
        List.fold_left
          (* and they must mantain the same shape *)
            (fun env (x, y) -> env >>= fun env -> SolverEnv.add_same_shape env x y )
          (Some env) vs
      with
      | None     -> true
      | Some env -> solve_assm_subst_var env assms goal x t )
  | _, T_Var _ -> solve_assm_shape env assms goal t2 t1
  | T_Atom _, T_Atom _ -> solve_ env assms goal
  | T_Atom _, _ -> true
  | T_Lam (_, t1), T_Lam (_, t2) -> solve_ env ((t1 =~: t2) :: assms) goal
  | T_Lam _, _ -> true
  | T_App (t1, t1'), T_App (t2, t2') -> solve_ env ((t1 =~: t2) :: (t1' =~: t2') :: assms) goal
  | T_App _, _ -> true
  | T_Fun f1, T_Fun f2 -> f1 <> f2 || solve_ env assms goal
  | T_Fun _, _ -> true

and solve_assm_subshape env assms goal t1 = function
  | T_Var {symb= x; _} -> (
    match SolverEnv.add_subshape env t1 x with
    | Some env -> solve_ env assms goal
    | None     -> true )
  | T_Lam (_, t2)      -> solve_assm_shape_and_subshape env assms goal t1 t2
  | T_App (t2, t2')    ->
      solve_assm_shape_and_subshape env assms goal t1 t2
      && solve_assm_shape_and_subshape env assms goal t1 t2'
  | T_Atom _ | T_Fun _ -> true

and solve_assm_shape_and_subshape env assms goal t1 t2 =
  solve_assm_shape env assms goal t1 t2 && solve_assm_subshape env assms goal t1 t2

and solve_assm_subst_var env assms goal x t =
  match SolverEnv.subst_var env x t with
  | None                  -> true
  | Some (env, env_assms) ->
      let assms = List.map (subst_var_in_constr x t) assms in
      let goal = subst_var_in_constr x t goal in
      solve_ env (env_assms @ assms) goal

let solve = solve_ SolverEnv.empty []

let solve_with_assumptions = solve_ SolverEnv.empty

let ( |-: ) = solve_with_assumptions
