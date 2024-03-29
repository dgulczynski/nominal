open Types
open Prelude
open Permutation
open SolverTypes

let fresh {perm= pi; symb= a} t = a #: (permute_term (reverse pi) t)

let reduce env =
  let update (env, assms) = function
    | SC_Fresh (a, T_Atom {perm= []; symb= b}) | SC_AtomNeq (a, {perm= []; symb= b}) ->
      (*   Γ, (a =/= b) ∪ Δ |- c  *)
      (* ------------------------ *)
      (*  (a =/= b) :: Γ, Δ |- c  *)
      (SolverEnv.add_neq a b =<< env, assms)
    | SC_Fresh (a, T_Var {perm= []; symb= x}) ->
      (*   Γ, (a # x) ∪ Δ |- c  *)
      (* ---------------------- *)
      (*  (a # x) :: Γ, Δ |- c  *)
      (SolverEnv.add_fresh a x <$> env, assms)
    | assm -> (env, assm :: assms)
  in
  on_snd List.rev (* Keep original order of assumptions not reduced *) % List.fold_left update (Some env, [])

let rec solve env assms goal =
  match reduce env assms with
  | None, _ -> true
  | Some env, [] -> solve_by_case env goal
  | Some env, assm :: assms -> solve_assm_by_case env assms goal assm

and solve_by_case env goal =
  match goal with
  | SC_Eq (t1, t2) -> solve_eq env t1 t2
  | SC_AtomEq (a, alpha) -> solve_eq env (atom a) (atom' alpha)
  | SC_Fresh (a, t) -> solve_fresh env a t
  | SC_AtomNeq (a, alpha) -> solve_fresh env a (atom' alpha)
  | SC_Shape (s1, s2) -> solve_shape env s1 s2
  | SC_Subshape (s1, s2) -> solve_subshape env s1 s2
  | SC_Symbol s -> solve_symbol env s

and solve_assm_by_case env assms goal assm =
  match assm with
  | SC_Eq (t1, t2) -> solve_assm_eq env assms goal t1 t2
  | SC_AtomEq (a, b) -> solve_assm_eq env assms goal (atom a) (atom' b)
  | SC_Fresh (a, t) -> solve_assm_fresh env assms goal a t
  | SC_AtomNeq (a, b) -> solve_assm_fresh env assms goal a (atom' b)
  | SC_Shape (s1, s2) -> solve_assm_shape env assms goal s1 s2
  | SC_Subshape (s1, s2) -> solve_assm_subshape env assms goal s1 s2
  | SC_Symbol s -> solve_assm_symbol env assms goal s

and solve_eq env e1 e2 : bool =
  match (e1, e2) with
  | T_Atom {perm= []; symb= a}, T_Atom {perm; symb= b} -> (
    match outer_swap perm with
    | None ->
      (* ---------------- *)
      (*  [], Δ |- a = a  *)
      a = b
    | Some (swap, pi) ->
      (*  [ a # a1, a # a2 ], Δ |-  a = π b  *)
      (*  [ a = a1, a # a2 ], Δ |- a2 = π b  *)
      (*          [ a = a2 ], Δ |- a1 = π b  *)
      (* ----------------------------------- *)
      (*        [], Δ |- a = [a1 a2]π b      *)
      let gen_goal a = atom' a =: atom' {perm= pi; symb= b} in
      solve_swap_cases env a swap (const []) gen_goal )
  | T_Atom {perm= pi; symb= a}, T_Atom b ->
    (*  [], Δ |- a = (rev π @ π') b  *)
    (* ----------------------------- *)
    (*     [], Δ |- π a = π' b       *)
    let a' = atom a in
    let b' = atom' (permute (reverse pi) b) in
    solve_eq env a' b'
  | T_Atom _, _ -> false
  | T_Var {perm= []; symb= x}, T_Var {perm= pi; symb= x'} when x = x' ->
    (*  [], Δ |- π idempotent on x  *)
    (* --------------------------- *)
    (*       [], Δ |- x = π x       *)
    permutation_idempotent env pi x
  | T_Var {perm= pi; symb= x}, T_Var {symb= x'; _} when x = x' ->
    (*  [], Δ |- x = (rev π @ π') x  *)
    (* ---------------------------- *)
    (*     [], Δ |- π x = π' x       *)
    solve_eq env (var x) (permute_term (reverse pi) e2)
  | T_Var _, _ -> false
  | T_Lam (a1, t1), T_Lam (a2, t2) ->
    (*    [], Δ |- a1 # (a2.e2)   *)
    (*  [], Δ |- e1 = [a1 a2] e2  *)
    (* ------------------------- *)
    (*   [], Δ |- a1.e1 = a2.e2   *)
    solve env [] $ fresh a1 e2 && solve_eq env t1 $ permute_term [(a1, a2)] t2
  | T_Lam _, _ -> false
  | T_App (t1, t2), T_App (t1', t2') ->
    (*      [], Δ |- e1 = e2      *)
    (*     [], Δ |- e1' = e2'     *)
    (* ------------------------- *)
    (*  [], Δ |- e1 e1' = e2 e2'  *)
    solve_eq env t1 t1' && solve_eq env t2 t2'
  | T_App _, _ -> false
  | T_Fun f1, T_Fun f2 ->
    (* --------------- *)
    (*  [], Δ |- f = f  *)
    f1 = f2
  | T_Fun _, _ -> false

and permutation_idempotent env pi x =
  (*  ∀ a ∈ π. ([], Δ |- a = π a  ∨  [], Δ |- a # x)  *)
  (* ---------------------------------------------- *)
  (*            [], Δ |- π idempotent on x           *)
  let test ({perm; symb= a} as alpha) =
    solve_eq env (atom' alpha) (atom' (permute pi alpha)) || solve_fresh env a (var' {perm= reverse perm; symb= x})
  in
  List.for_all test (free_vars_of pi)

and solve_fresh env a e =
  let solve_fresh_swap swap t = solve_swap_cases env a swap (const []) (flip fresh t) in
  match e with
  | T_Atom {perm; symb= b} -> (
    match outer_swap perm with
    | None ->
      (*  (a =/= b) ∈ Δ  *)
      (* --------------- *)
      (*  [], Δ |- a # b  *)
      SolverEnv.is_neq env a b
    | Some (swap, pi) ->
      (*  [ a =/= a1, a =/= a2 ], Δ |-  a # π b  *)
      (*    [ a = a1, a =/= a2 ], Δ |- a2 # π b  *)
      (*               [ a = a2 ], Δ |- a1 # π b  *)
      (* --------------------------------------- *)
      (*           [], Δ |- a # [a1 a2]π b       *)
      solve_fresh_swap swap (atom' {perm= pi; symb= b}) )
  | T_Var {perm; symb= x} -> (
    match outer_swap perm with
    | None ->
      SolverEnv.is_fresh env a x || SolverEnv.is_symbol env x
      (*   (a # x) ∈ Δ          (symbol x) ∈ Δ  *)
      (* ----------------    ------------------ *)
      (*  [], Δ |- a # x       [], Δ |- a # x   *)
    | Some (swap, pi) ->
      (*  [ a # a1, a # a2 ], Δ |-  a # π x  *)
      (*  [ a = a1, a # a2 ], Δ |- a2 # π x  *)
      (*          [ a = a2 ], Δ |- a1 # π x  *)
      (* ----------------------------------- *)
      (*         [], Δ |- a # [a1 a2]π x     *)
      solve_fresh_swap swap $ var' {perm= pi; symb= x} )
  | T_Lam (alpha, t) ->
    (*  [ a # b ], Δ |- a # e  *)
    (* ----------------------- *)
    (*    [], Δ |- a # b.e     *)
    solve env [a =/=: alpha] $ a #: t
  | T_App (t1, t2) ->
    (*   [], Δ |- a # e1    *)
    (*   [], Δ |- a # e2    *)
    (* -------------------- *)
    (*  [], Δ |- a # e1 e2  *)
    solve_fresh env a t1 && solve_fresh env a t2
  | T_Fun _ ->
    (* absurd *)
    true

and solve_shape env s1 s2 =
  match (s1, s2) with
  | S_Var x1, S_Var x2 ->
    (*    (x1 ~ x2) ∈ Δ   *)
    (* ------------------ *)
    (*  [], Δ |- x1 ~ x2  *)
    SolverEnv.are_same_shape env x1 x2
  | S_Var x, s | s, S_Var x -> (
    match SolverEnv.get_shape env x with
    | None -> false
    (*   (x ~ z) ∈ Δ    *)
    (*  [], Δ |- z ~ s  *)
    (* ---------------- *)
    (*  [], Δ |- x ~ z  *)
    | Some sx -> solve_shape env sx s )
  | S_Atom, S_Atom ->
    (* ------------------- *)
    (*   [], Δ |- a1 ~ a2   *)
    true
  | S_Atom, _ -> false
  | S_Lam s1, S_Lam s2 ->
    (*    [], Δ |- e1 ~ e2    *)
    (* ---------------------- *)
    (*  [], Δ |- _.e1 ~ _.e2  *)
    solve_shape env s1 s2
  | S_Lam _, _ -> false
  | S_App (s1, s1'), S_App (s2, s2') ->
    (*      [], Δ |- e1 ~ e2      *)
    (*     [], Δ |- e1' ~ e2'     *)
    (* -------------------------- *)
    (*  [], Δ |- e1 e1' ~ e2 e2'  *)
    solve_shape env s1 s2 && solve_shape env s1' s2'
  | S_App _, _ -> false
  | S_Fun f1, S_Fun f2 ->
    (* ---------------- *)
    (*  [], Δ |- f ~ f  *)
    f1 = f2
  | S_Fun _, _ -> false

and solve_subshape env t1 = function
  | S_Var x ->
    (*    (t2 < x) ∈ Δ              (t2 < x) ∈ Δ    *)
    (*  [], Δ |- t1 ~ t2          [], Δ |- t1 < t2  *)
    (* -------------------      ------------------- *)
    (*  [], Δ |- t1 < x           [], Δ |- t1 < x   *)
    List.exists (solve_shape_or_subshape env t1) (SolverEnv.get_subshapes env x)
  | S_Lam t2 ->
    (*   [], Δ |- t1 ~ t2          [], Δ |- t1 < t2   *)
    (* --------------------      -------------------- *)
    (*  [], Δ |- t1 < _.t2        [], Δ |- t1 < _.t2  *)
    solve_shape_or_subshape env t1 t2
  | S_App (t2, t2') ->
    (*   [], Δ |- t1 ~ t2         [], Δ |- t1 < t2          [], Δ |- t1 ~ t2'         [], Δ |- t1 < t2'    *)
    (* ----------------------   ----------------------   -----------------------   ----------------------- *)
    (*  [], Δ |- t1 < t2 t2'     [], Δ |- t1 < t2 t2'      [], Δ |- t1 < t2 t2'      [], Δ |- t1 < t2 t2'  *)
    solve_shape_or_subshape env t1 t2 || solve_shape_or_subshape env t1 t2'
  | S_Atom | S_Fun _ ->
    (* trivial *)
    false

and solve_shape_or_subshape env t1 t2 = solve_shape env t1 t2 || solve_subshape env t1 t2

and solve_symbol env = function
  | S_Fun _ ->
    (* ------------------- *)
    (*  [], Δ |- symbol f  *)
    true
  | S_Var x ->
    (*    (symbol x) ∈ Δ   *)
    (* ------------------- *)
    (*  [], Δ |- symbol x  *)
    SolverEnv.is_symbol env x
  | S_Atom | S_Lam _ | S_App _ ->
    (* trivial *)
    false

and solve_assm_fresh env assms goal a = function
  | T_Atom {perm= pi; symb= b} ->
    (*  (a # a1) :: (a # a2) :: ( a # π b) :: Γ, Δ |- c  *)
    (*  (a = a1) :: (a # a2) :: (a2 # π b) :: Γ, Δ |- c  *)
    (*              (a = a2) :: (a1 # π b) :: Γ, Δ |- c  *)
    (* ------------------------------------------------- *)
    (*                    (a # [a1 a2]π b) :: Γ, Δ |- c  *)
    let swap, pi = Option.get $ outer_swap pi in
    (* Here we use Option.get because we are sure that the permutation is non-empty, *)
    (* because if it was empty the assumption would already be merged into the env by the reduce function *)
    solve_swap_cases env a swap (fun a -> fresh a (atom' {perm= pi; symb= b}) :: assms) (const goal)
  | T_Var {perm= pi; symb= x} ->
    (*  (a # a1) :: (a # a2) :: ( a # π x) :: Γ, Δ |- c  *)
    (*  (a = a1) :: (a # a2) :: (a2 # π x) :: Γ, Δ |- c  *)
    (*              (a = a2) :: (a1 # π x) :: Γ, Δ |- c  *)
    (* ------------------------------------------------- *)
    (*                    (a # [a1 a2]π x) :: Γ, Δ |- c  *)
    let swap, pi = Option.get $ outer_swap pi in
    (* See comment above: we are sure the permutation is non-empty here *)
    solve_swap_cases env a swap (fun a -> fresh a (var' {perm= pi; symb= x}) :: assms) (const goal)
  | T_Lam (alpha, t) ->
    (*             (a = b) :: Γ, Δ |- c  *)
    (*  (a # b) :: (a # e) :: Γ, Δ |- c  *)
    (* --------------------------------- *)
    (*           (a # b.e) :: Γ, Δ |- c  *)
    solve env ((a ==: alpha) :: assms) goal && solve env ((a =/=: alpha) :: (a #: t) :: assms) goal
  | T_App (t1, t2) ->
    (*  (a # e1) :: (a # e2) :: Γ, Δ |- c  *)
    (* ----------------------------------- *)
    (*       (a # e1 e2) :: Γ, Δ |- c      *)
    solve env ((a #: t1) :: (a #: t2) :: assms) goal
  | T_Fun _ ->
    (*       Γ, Δ |- c        *)
    (* ---------------------- *)
    (*  (a # f) :: Γ, Δ |- c  *)
    solve env assms goal

and solve_assm_eq env assms goal t1 t2 =
  match (t1, t2) with
  | T_Var {perm= []; symb= x}, T_Var {perm= pi; symb= x'} when x = x' && permutation_idempotent env pi x ->
    (*  [], Δ |- π idempotent on x  *)
    (*           Γ, Δ |- c          *)
    (* ---------------------------- *)
    (*    (x = π x) :: Γ, Δ |- c    *)
    solve env assms goal
  | T_Var {perm= []; symb= x}, T_Var {perm= pi; symb= x'} when x = x' ->
    (*  (π idempotent on x) :: Γ, Δ |- c  *)
    (* ---------------------------------- *)
    (*            (x = π x) :: Γ, Δ |- c  *)
    let solve_with_assms assms = solve env assms goal in
    List.for_all solve_with_assms $ build_permutation_idempotent_assms pi x assms
  | T_Var {perm= _ :: _; symb= x}, T_Var {perm= []; symb= x'} when x = x' -> solve_assm_eq env assms goal t2 t1
  | T_Var {perm= []; symb= x}, t | t, T_Var {perm= []; symb= x} ->
    (*  Γ {x -> t}, Δ {x -> t} |- c {x -> t}  *)
    (* -------------------------------------- *)
    (*         (x = t) :: Γ, Δ |- c           *)
    let subst = subst_var_in_solver_constr x t in
    solve_assm_in_modified_env (SolverEnv.subst_var x t) env (List.map subst assms) (subst goal)
  | T_Var {perm= pi; symb= x}, t | t, T_Var {perm= pi; symb= x} ->
    (*  (x = (rev π) t) :: Γ, Δ |- c  *)
    (* ------------------------------ *)
    (*     (π x = t) :: Γ, Δ |- c     *)
    solve_assm_eq env assms goal (var x) (permute_term (reverse pi) t)
  | T_Atom {perm= []; symb= a}, T_Atom {perm= pi; symb= b} -> (
    match outer_swap pi with
    | None -> (
      match SolverEnv.subst_atom a b env with
      | None ->
        (*     (a =/= b) ∈ Δ      *)
        (* ---------------------- *)
        (*  (a = b) :: Γ, Δ |- c  *)
        true
      | Some env ->
        (*  Γ {a -> b}, Δ {a -> b} |- c {a -> b}  *)
        (* -------------------------------------- *)
        (*         (a = b) :: Γ, Δ |- c           *)
        let subst = subst_atom_in_solver_constr a $ pure b in
        solve env (List.map subst assms) (subst goal) )
    | Some (swap, pi) ->
      (*  (a # a1) :: (a # a2) :: ( a = π b) :: Γ, Δ |- c  *)
      (*  (a = a1) :: (a # a2) :: (a2 = π b) :: Γ, Δ |- c  *)
      (*              (a = a2) :: (a1 = π b) :: Γ, Δ |- c  *)
      (* ------------------------------------------------------- *)
      (*           (a = [a1 a2]π b) :: Γ, Δ |- c           *)
      solve_swap_cases env a swap (fun a -> (atom' a =: atom' {perm= pi; symb= b}) :: assms) (const goal) )
  | T_Atom {perm= pi; symb= a}, T_Atom beta ->
    (*  (a = (rev π @ π') b) :: Γ, Δ |- c  *)
    (* ----------------------------------- *)
    (*       (π a = π' b) :: Γ, Δ |- c     *)
    solve_assm_eq env assms goal (atom a) (atom' (permute pi beta))
  | T_Atom _, _ -> true
  | T_Lam (a1, t1), T_Lam (a2, t2) ->
    (*  (a1 # a2.e2) :: (e1 = [a1 a2] e2) :: Γ, Δ |- c  *)
    (* ------------------------------------------------ *)
    (*           (a1.e1 = a2.e2) :: Γ, Δ |- c           *)
    solve env (fresh a1 (lam a2 t2) :: (t1 =: permute_term [(a1, a2)] t2) :: assms) goal
  | T_Lam _, _ -> true
  | T_App (t1, t2), T_App (t1', t2') ->
    (*  (e1 = e2) :: (e1' = e2') :: Γ, Δ |- c  *)
    (* ------------------------------------------------ *)
    (*           e1 e1' = e2 e2' :: Γ, Δ |- c           *)
    solve env ((t1 =: t1') :: (t2 =: t2') :: assms) goal
  | T_App _, _ -> true
  | T_Fun f, T_Fun f' ->
    (*       f1 =/= f2                   Γ, Δ |- c       *)
    (* ------------------------   ---------------------- *)
    (*  (f1 = f2) :: Γ, Δ |- c     (f = f) :: Γ, Δ |- c  *)
    f <> f' || solve env assms goal
  | T_Fun _, _ -> true

(** Builds a list of assumption-lists that exhaust all possibilities that ensuring [x =: π x] *)
and build_permutation_idempotent_assms pi x assms =
  (*  (∀ a ∈ π. a = π a  ∨  a # x) :: Γ, Δ |- c  *)
  (* ------------------------------------------- *)
  (*           (π idempotent on x) :: Γ, Δ |- c  *)
  let add_atom_assms assmss a =
    let a_fresh = fresh a (var x) in
    let a_idemp = atom' a =: atom' (permute pi a) in
    let assmss_cons c = List.map (List.cons c) assmss in
    assmss_cons a_fresh @ assmss_cons a_idemp
  in
  List.fold_left add_atom_assms [assms] (free_vars_of pi)

and solve_swap_cases env a (alpha1, alpha2) assm_gen goal_gen =
  solve env ((a =/=: alpha1) :: (a =/=: alpha2) :: assm_gen (pure a)) (goal_gen (pure a))
  && solve env ((a ==: alpha1) :: (a =/=: alpha2) :: assm_gen alpha2) (goal_gen alpha2)
  && solve env ((a ==: alpha2) :: assm_gen alpha1) (goal_gen alpha1)

and solve_assm_shape env assms goal t1 t2 =
  match (t1, t2) with
  | S_Var x1, S_Var x2 ->
    (*   Γ, (x1 ~ x2) ∪ Δ |- c  *)
    (* ------------------------ *)
    (*  (x1 ~ x2) :: Γ, Δ |- c  *)
    solve_assm_in_modified_env (SolverEnv.add_same_shape x1 x2) env assms goal
  | S_Var x, s ->
    (*   Γ, (x ~ s) ∪ Δ |- c  *)
    (* ---------------------- *)
    (*  (x ~ s) :: Γ, Δ |- c  *)
    solve_assm_in_modified_env (SolverEnv.set_var_shape x s) env assms goal
  | _, S_Var _ -> solve_assm_shape env assms goal t2 t1
  | S_Atom, S_Atom ->
    (*         Γ, Δ |- c        *)
    (* ------------------------ *)
    (*  (a1 ~ a2) :: Γ, Δ |- c  *)
    solve env assms goal
  | S_Atom, _ -> true
  | S_Lam t1, S_Lam t2 ->
    (*      (e1 ~ e2) :: Γ, Δ |- c    *)
    (* --------------------------------- *)
    (*  (a1.e1 ~ a2.e2) :: Γ, Δ |- c  *)
    solve env ((t1 =~: t2) :: assms) goal
  | S_Lam _, _ -> true
  | S_App (t1, t1'), S_App (t2, t2') ->
    (*  (e1 ~ e2) :: (e1' ~ e2') :: Γ, Δ |- c  *)
    (* --------------------------------------------- *)
    (*      (e1 e1' ~ e2 e2') :: Γ, Δ |- c     *)
    solve env ((t1 =~: t2) :: (t1' =~: t2') :: assms) goal
  | S_App _, _ -> true
  | S_Fun f1, S_Fun f2 ->
    (*      f1 =/= f2                    Γ, Δ |- c       *)
    (* ------------------------   ---------------------- *)
    (*  (f1 ~ f2) :: Γ, Δ |- c     (f ~ f) :: Γ, Δ |- c  *)
    f1 <> f2 || solve env assms goal
  | S_Fun _, _ -> true

and solve_assm_subshape env assms goal t1 = function
  | S_Var x ->
    (*  Γ, (t1 < x) ∪ Δ |- c  *)
    (* ----------------------- *)
    (*  (t1 < x) :: Γ, Δ |- c  *)
    solve_assm_in_modified_env (SolverEnv.add_subshape t1 x) env assms goal
  | S_Lam t2 ->
    (*    (t1 ~ t2) :: Γ, Δ |- c  *)
    (*    (t1 < t2) :: Γ, Δ |- c  *)
    (* -------------------------- *)
    (*  (t1 < _.t2) :: Γ, Δ |- c  *)
    solve_assm_shape_and_subshape env assms goal t1 t2
  | S_App (t2, t2') ->
    (*      (t1 ~ t2) :: Γ, Δ |- c  *)
    (*      (t1 < t2) :: Γ, Δ |- c  *)
    (*     (t1 ~ t2') :: Γ, Δ |- c  *)
    (*     (t1 < t2') :: Γ, Δ |- c  *)
    (* ---------------------------- *)
    (*  (t1 < t2 t2') :: Γ, Δ |- c  *)
    solve_assm_shape_and_subshape env assms goal t1 t2 && solve_assm_shape_and_subshape env assms goal t1 t2'
  | S_Atom | S_Fun _ ->
    (* absurd *)
    true

and solve_assm_shape_and_subshape env assms goal t1 t2 =
  solve_assm_shape env assms goal t1 t2 && solve_assm_subshape env assms goal t1 t2

and solve_assm_symbol env assms goal t =
  match t with
  | S_Fun _ ->
    (*          Γ, Δ |- c         *)
    (* -------------------------- *)
    (*  (symbol f) :: Γ, Δ |- c  *)
    solve env assms goal
  | S_Var x -> solve_assm_in_modified_env (SolverEnv.add_symbol x) env assms goal
  | S_Atom | S_Lam _ | S_App _ ->
    (* absurd *)
    true

and solve_assm_in_modified_env add_assm_to_env env assms goal =
  match add_assm_to_env env with
  | None -> true
  | Some (env, env_assms) -> solve env (env_assms @ assms) goal

let solve_with_assms assms goal =
  let solver_assms = List.map from_constr assms in
  let solver_goal = from_constr goal in
  solve SolverEnv.empty solver_assms solver_goal

let ( |-: ) = solve_with_assms

let ( ||-: ) = solve_with_assms []

let absurd =
  let t = symb "absurd" in
  C_Subshape (t, t)
