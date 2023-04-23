open Types
open Common
open Permutation
open Substitution
open Utils

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
  | C_Symbol t           -> solve_symbol env t

and solve_assm_by_case env assms goal = function
  | C_Eq (t1, t2)       -> solve_assm_eq env assms goal t1 t2
  | C_AtomEq (a, b)     -> solve_assm_eq env assms goal (T_Atom (pure a)) (T_Atom b)
  | C_Fresh (a, t)      -> solve_assm_fresh env assms goal a t
  | C_AtomNeq (a, b)    -> solve_assm_fresh env assms goal a (T_Atom b)
  | C_Shape (t1, t2)    -> solve_assm_shape env assms goal t1 t2
  | C_Subshape (t1, t2) -> solve_assm_subshape env assms goal t1 t2
  | C_Symbol t          -> solve_assm_symbol env assms goal t

and solve_eq env assms e1 e2 =
  match (e1, e2) with
  | T_Atom {perm= []; symb= a}, T_Atom {perm; symb= b} -> (
    match outer_swap perm with
    | None            ->
        (* ----------------- *)
        (*    Γ |- a = a     *)
        a = b
    | Some (swap, pi) ->
        (*  (a # a1) :: (a # a2) :: Γ |-  a = π b  *)
        (*  (a = a1) :: (a # a2) :: Γ |- a2 = π b  *)
        (*              (a = a2) :: Γ |- a1 = π b  *)
        (* --------------------------------------- *)
        (*            Γ |- a = [a1 a2]π b          *)
        let gen_goal a = T_Atom a =: T_Atom {perm= pi; symb= b} in
        solve_swap_cases env a swap (const assms) gen_goal )
  | T_Atom {perm= pi; symb= a}, T_Atom b ->
      (*  Γ |- a = (rev π @ π') b  *)
      (* ------------------------- *)
      (*     Γ |- π a = π' b       *)
      let a' = T_Atom (pure a) in
      let b' = T_Atom (permute (reverse pi) b) in
      solve_eq env assms a' b'
  | T_Atom _, _ -> false
  | T_Var {perm= []; symb= x}, T_Var {perm= pi; symb= x'} when x = x' ->
      (*  Γ |- π idempotent on x  *)
      (* ------------------------ *)
      (*       Γ |- x = π x       *)
      permutation_idempotent env assms pi x
  | T_Var {perm= pi; symb= x}, T_Var {symb= x'; _} when x = x' ->
      (*  Γ |- x = (rev π @ π') x  *)
      (* ------------------------- *)
      (*     Γ |- π x = π' x       *)
      solve_eq env assms $ var x $ permute_term (reverse pi) e2
  | T_Var _, _ -> false
  | T_Lam (({perm= pi; symb= a1} as alpha1), t1), T_Lam (alpha2, t2) ->
      (*      Γ |- a1 # e2      *)
      (*  Γ |- e1 = [a1 a2] e2  *)
      (* ---------------------- *)
      (*   Γ |- a1.e1 = a2.e2   *)
      solve_fresh env assms a1 $ permute_term (reverse pi) e2
      && solve_eq env assms t1 $ permute_term [(alpha1, alpha2)] t2
  | T_Lam _, _ -> false
  | T_App (t1, t2), T_App (t1', t2') ->
      (*      Γ |- e1 = e2      *)
      (*     Γ |- e1' = e2'     *)
      (* ---------------------- *)
      (*  Γ |- e1 e1' = e2 e2'  *)
      solve_eq env assms t1 t1' && solve_eq env assms t2 t2'
  | T_App _, _ -> false
  | T_Fun f1, T_Fun f2 ->
      (* ------------ *)
      (*  Γ |- f = f  *)
      f1 = f2
  | T_Fun _, _ -> false

and permutation_idempotent env assms pi x =
  (* ∀ a ∈ π. Γ |- a = π a  ∨  a # x  *)
  (* -------------------------------- *)
  (*       Γ |- π idempotent on x     *)
  let test ({perm; symb= a} as alpha) =
    solve_eq env assms (T_Atom alpha) (T_Atom (permute pi alpha))
    || solve_fresh env assms a $ T_Var {perm= reverse perm; symb= x}
  in
  List.for_all test (free_vars_of pi)

and solve_fresh env assms a e =
  let solve_fresh_swap swap t = solve_swap_cases env a swap (const assms) (flip fresh t) in
  match e with
  | T_Atom {perm; symb= b} -> (
    match outer_swap perm with
    | None            ->
        (*   (a =/= b) ∈ Γ   *)
        (* ----------------- *)
        (*    Γ |- a # b     *)
        SolverEnv.is_neq env a b
    | Some (swap, pi) ->
        (*  (a # a1) :: (a # a2) :: Γ |-  a # π b  *)
        (*  (a = a1) :: (a # a2) :: Γ |- a2 # π b  *)
        (*              (a = a2) :: Γ |- a1 # π b  *)
        (* --------------------------------------- *)
        (*            Γ |- a # [a1 a2]π b          *)
        solve_fresh_swap swap $ T_Atom {perm= pi; symb= b} )
  | T_Var {perm; symb= x}  -> (
    match outer_swap perm with
    | None            ->
        SolverEnv.is_fresh env a x
        (*  (a # x) ∈ Γ  *)
        (* ------------- *)
        (*   Γ |- a # x  *)
    | Some (swap, pi) ->
        (*  (a # a1) :: (a # a2) :: Γ |-  a # π x  *)
        (*  (a = a1) :: (a # a2) :: Γ |- a2 # π x  *)
        (*              (a = a2) :: Γ |- a1 # π x  *)
        (* --------------------------------------- *)
        (*            Γ |- a # [a1 a2]π x          *)
        solve_fresh_swap swap $ T_Var {perm= pi; symb= x} )
  | T_Lam (alpha, t)       ->
      (*  (a # b) :: Γ |- a # e  *)
      (* ----------------------- *)
      (*      Γ |- a # b.e       *)
      solve_ env ((a =/=: alpha) :: assms) a #: t
  | T_App (t1, t2)         ->
      (*    Γ |- a # e1    *)
      (*    Γ |- a # e2    *)
      (* ----------------- *)
      (*   Γ |- a # e1 e2  *)
      solve_fresh env assms a t1 && solve_fresh env assms a t2
  | T_Fun _                ->
      (* absurd *)
      true

and solve_shape env assms t1 t2 =
  match (t1, t2) with
  | T_Var {symb= x1; _}, T_Var {symb= x2; _} ->
      (*   (x1 ~ x2) ∈ Γ  *)
      (* ---------------- *)
      (*   Γ |- x1 ~ x2   *)
      SolverEnv.are_same_shape env x1 x2
  | T_Var _, _ -> false
  | T_Atom _, T_Atom _ ->
      (* ---------------- *)
      (*   Γ |- a1 ~ a2   *)
      true
  | T_Atom _, _ -> false
  | T_Lam (_, t1), T_Lam (_, t2) ->
      (*     Γ |- e1 ~ e2     *)
      (* -------------------- *)
      (*  Γ |- a1.e1 ~ a2.e2  *)
      solve_shape env assms t1 t2
  | T_Lam _, _ -> false
  | T_App (t1, t1'), T_App (t2, t2') ->
      (*      Γ |- e1 ~ e2      *)
      (*     Γ |- e1' ~ e2'     *)
      (* ---------------------- *)
      (*  Γ |- e1 e1' ~ e2 e2'  *)
      solve_shape env assms t1 t2 && solve_shape env assms t1' t2'
  | T_App _, _ -> false
  | T_Fun f1, T_Fun f2 ->
      (* ------------ *)
      (*  Γ |- f ~ f  *)
      f1 = f2
  | T_Fun _, _ -> false

and solve_subshape env assms t1 = function
  | T_Var {symb= x; _} ->
      (*   (t2 < x) ∈ Γ          (t2 < x) ∈ Γ   *)
      (*   Γ |- t1 ~ t2          Γ |- t1 < t2   *)
      (* ----------------      ---------------- *)
      (*   Γ |- t1 < x           Γ |- t1 < x    *)
      List.exists (solve_shape_or_subshape env assms t1) $ SolverEnv.get_subshapes env x
  | T_Lam (_, t2)      ->
      (*   Γ |- t1 ~ t2          Γ |- t1 < t2   *)
      (* ----------------      ---------------- *)
      (*  Γ |- t1 < _.t2        Γ |- t1 < _.t2  *)
      solve_shape_or_subshape env assms t1 t2
  | T_App (t2, t2')    ->
      (*   Γ |- t1 ~ t2         Γ |- t1 < t2          Γ |- t1 ~ t2'         Γ |- t1 < t2'    *)
      (* ------------------   ------------------   -------------------   ------------------- *)
      (*  Γ |- t1 < t2 t2'     Γ |- t1 < t2 t2'      Γ |- t1 < t2 t2'      Γ |- t1 < t2 t2'  *)
      solve_shape_or_subshape env assms t1 t2 || solve_shape_or_subshape env assms t1 t2'
  | T_Atom _ | T_Fun _ ->
      (* trivial *)
      false

and solve_shape_or_subshape env assms t1 t2 = solve_shape env assms t1 t2 || solve_subshape env assms t1 t2

and solve_symbol env t =
  match t with
  | T_Fun _                      ->
      (* --------------- *)
      (*  Γ |- symbol f  *)
      true
  | T_Var {symb= x; _}           ->
      (*  (symbol? x) ∈ Γ  *)
      (* ----------------- *)
      (*   Γ |- symbol? x  *)
      SolverEnv.is_symbol env x
  | T_Atom _ | T_Lam _ | T_App _ ->
      (* trivial *)
      false

and solve_assm_fresh env assms goal a = function
  | T_Atom {perm= pi; symb= b} ->
      (*  (a # a1) :: (a # a2) :: ( a # π b) :: Γ |- c  *)
      (*  (a = a1) :: (a # a2) :: (a2 # π b) :: Γ |- c  *)
      (*              (a = a2) :: (a1 # π b) :: Γ |- c  *)
      (* ---------------------------------------------- *)
      (*                    (a # [a1 a2]π b) :: Γ |- c  *)
      let swap, pi = Option.get $ outer_swap pi in
      (* Here we use Option.get because we are sure that the permutation is non-empty, *)
      (* because if it was empty the assumption would already be merged into the env by the reduce function *)
      solve_swap_cases env a swap (fun a -> fresh a (T_Atom {perm= pi; symb= b}) :: assms) (const goal)
  | T_Var {perm= pi; symb= x}  ->
      (*  (a # a1) :: (a # a2) :: ( a # π x) :: Γ |- c  *)
      (*  (a = a1) :: (a # a2) :: (a2 # π x) :: Γ |- c  *)
      (*              (a = a2) :: (a1 # π x) :: Γ |- c  *)
      (* ---------------------------------------------- *)
      (*                    (a # [a1 a2]π x) :: Γ |- c  *)
      let swap, pi = Option.get $ outer_swap pi in
      (* See comment above: we are sure the permutation is non-empty here *)
      solve_swap_cases env a swap (fun a -> fresh a (T_Var {perm= pi; symb= x}) :: assms) (const goal)
  | T_Lam (alpha, t)           ->
      (*             (a = b) :: Γ |- c  *)
      (*  (a # b) :: (a # e) :: Γ |- c  *)
      (* ------------------------------ *)
      (*           (a # b.t) :: Γ |- c  *)
      solve_ env ((a ==: alpha) :: assms) goal && solve_ env ((a =/=: alpha) :: (a #: t) :: assms) goal
  | T_App (t1, t2)             ->
      (*  (a # e1) :: (a # e2) :: Γ |- c  *)
      (* -------------------------------- *)
      (*       (a # e1 e2) :: Γ |- c      *)
      solve_ env ((a #: t1) :: (a #: t2) :: assms) goal
  | T_Fun _                    ->
      (* trivial *)
      solve_ env assms goal

and solve_assm_eq env assms goal t1 t2 =
  match (t1, t2) with
  | T_Atom {perm= []; symb= a}, T_Atom {perm= pi; symb= b} -> (
    match outer_swap pi with
    | None            -> (
      match SolverEnv.subst_atom env a b with
      | None     ->
          (*      (a # b) ∈ Γ     *)
          (* -------------------- *)
          (*   (a = b) :: Γ |- c  *)
          true
      | Some env ->
          (*  Γ {a -> b} |- c {a -> b} *)
          (* ------------------------- *)
          (*     (a = b) :: Γ |- c     *)
          let b = pure b in
          let assms = List.map (subst_atom_in_constr a b) assms in
          let goal = subst_atom_in_constr a b goal in
          solve_ env assms goal )
    | Some (swap, pi) ->
        (*  (a # a1) :: (a # a2) :: ( a = π b) :: Γ |- c  *)
        (*  (a = a1) :: (a # a2) :: (a2 = π b) :: Γ |- c  *)
        (*              (a = a2) :: (a1 = π b) :: Γ |- c  *)
        (* ---------------------------------------------- *)
        (*           (a = [a1 a2]π b) :: Γ |- c           *)
        solve_swap_cases env a swap (fun a -> (T_Atom a =: T_Atom {perm= pi; symb= b}) :: assms) (const goal)
    )
  | T_Atom {perm= pi; symb= a}, T_Atom beta ->
      (*  (a = (rev π @ π') b) :: Γ |- c  *)
      (* -------------------------------- *)
      (*       (π a = π' b) :: Γ |- c     *)
      solve_assm_eq env assms goal $ T_Atom {perm= []; symb= a} $ T_Atom (permute pi beta)
  | T_Atom _, _ -> true
  | T_Var {perm= []; symb= x}, T_Var {perm= pi; symb= x'} when x = x' && permutation_idempotent env assms pi x
    ->
      (*  Γ |- π idempotent on x  *)
      (*           Γ |- c         *)
      (* ------------------------ *)
      (*    (x = π x) :: Γ |- c   *)
      solve_ env assms goal
  | T_Var {perm= []; symb= x}, t | t, T_Var {perm= []; symb= x} ->
      (*  Γ {x -> t} |- c {x -> t}  *)
      (* -------------------------- *)
      (*     (x = t) :: Γ |- c      *)
      solve_assm_subst_var env assms goal x t
  | T_Var {perm= pi; symb= x}, t | t, T_Var {perm= pi; symb= x} ->
      (*  (x = (rev π) t) :: Γ |- c  *)
      (* --------------------------- *)
      (*     (π x = t) :: Γ |- c     *)
      solve_assm_eq env assms goal $ var x $ permute_term pi t
  | T_Lam (a1, t1), T_Lam ((a2 as a2_bind), t2) ->
      (*  (a1 # e2) :: (e1 = [a1 a2] e2) :: Γ |- c  *)
      (* ------------------------------------------ *)
      (*          (a1.e1 = a2.e2) :: Γ |- c         *)
      solve_ env (fresh a1 (T_Lam (a2_bind, t2)) :: (t1 =: permute_term [(a1, a2)] t2) :: assms) goal
  | T_Lam _, _ -> true
  | T_App (t1, t2), T_App (t1', t2') -> solve_ env ((t1 =: t1') :: (t2 =: t2') :: assms) goal
  | T_App _, _ -> true
  | T_Fun f, T_Fun f' ->
      (*       f1 =/= f2                Γ |- c       *)
      (* ---------------------   ------------------- *)
      (*  (f1 = f2) :: Γ |- c     (f = f) :: Γ |- c  *)
      f <> f' || solve_ env assms goal
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
      (* TODO: do not do this like that *)
      let t, vs = term_of_shape (shape_of_term t) in
      (* Is this sound? Does it ever stop? Maybe not *)
      (* vs is the mapping from fresh variables to variables of original term t *)
      match
        List.fold_left
          (* and they must mantain the same shape *)
            (fun env (x, y) -> env >>= fun env -> SolverEnv.add_same_shape env x y )
          (Some env) vs
      with
      | None     -> true
      | Some env -> solve_assm_subst_var env assms goal x t )
  | _, T_Var _ -> solve_assm_shape env assms goal t2 t1
  | T_Atom _, T_Atom _ ->
      (*         Γ |- c        *)
      (* --------------------- *)
      (*  (a1 ~ a2) :: Γ |- c  *)
      solve_ env assms goal
  | T_Atom _, _ -> true
  | T_Lam (_, t1), T_Lam (_, t2) ->
      (*      (e1 ~ e2) :: Γ |- c    *)
      (* --------------------------- *)
      (*  (a1.e1 ~ a2.e2) :: Γ |- c  *)
      solve_ env ((t1 =~: t2) :: assms) goal
  | T_Lam _, _ -> true
  | T_App (t1, t1'), T_App (t2, t2') ->
      (*  (e1 ~ e2) :: (e1' ~ e2') :: Γ |- c  *)
      (* ------------------------------------ *)
      (*      (e1 e1' ~ e2 e2') :: Γ |- c     *)
      solve_ env ((t1 =~: t2) :: (t1' =~: t2') :: assms) goal
  | T_App _, _ -> true
  | T_Fun f1, T_Fun f2 ->
      (*      f1 =/= f2                 Γ |- c       *)
      (* ---------------------   ------------------- *)
      (*  (f1 ~ f2) :: Γ |- c     (f ~ f) :: Γ |- c  *)
      f1 <> f2 || solve_ env assms goal
  | T_Fun _, _ -> true

and solve_assm_subshape env assms goal t1 = function
  | T_Var {symb= x; _} -> (
    match SolverEnv.add_subshape env t1 x with
    | Some env -> solve_ env assms goal
    | None     -> true )
  | T_Lam (_, t2)      ->
      (*    (t1 ~ t2) :: Γ |- c  *)
      (*    (t1 < t2) :: Γ |- c  *)
      (* ----------------------- *)
      (*  (t1 < _.t2) :: Γ |- c  *)
      solve_assm_shape_and_subshape env assms goal t1 t2
  | T_App (t2, t2')    ->
      (*     (t1 ~ t2) :: Γ |- c   *)
      (*     (t1 < t2) :: Γ |- c   *)
      (*    (t1 ~ t2') :: Γ |- c   *)
      (*    (t1 < t2') :: Γ |- c   *)
      (* ------------------------- *)
      (*  (t1 < t2 t2') :: Γ |- c  *)
      solve_assm_shape_and_subshape env assms goal t1 t2
      && solve_assm_shape_and_subshape env assms goal t1 t2'
  | T_Atom _ | T_Fun _ ->
      (* absurd *)
      true

and solve_assm_shape_and_subshape env assms goal t1 t2 =
  solve_assm_shape env assms goal t1 t2 && solve_assm_subshape env assms goal t1 t2

and solve_assm_symbol env assms goal t =
  match t with
  | T_Fun _                      ->
      (*          Γ |- c         *)
      (* ----------------------- *)
      (*  (symbol? f) :: Γ |- c  *)
      solve_ env assms goal
  | T_Var {symb= x; _}           -> (
    match SolverEnv.add_symbol env x with
    | Some env -> solve_ env assms goal
    | None     -> true )
  | T_Atom _ | T_Lam _ | T_App _ ->
      (* absurd *)
      true

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

let absurd =
  let t = T_Fun "" in
  t <: t
