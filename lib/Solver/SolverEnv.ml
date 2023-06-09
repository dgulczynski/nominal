open Types
open Prelude
open Permutation
open SolverTypes

module Atom = struct
  type t = atom

  let compare = compare
end

module Var = struct
  type t = var

  let compare = compare
end

module AtomMap = Map.Make (Atom)
module VarMap = Map.Make (Var)

type t =
  { symbols: var list  (** [x :: _ ] means [symbol x]*)
  ; neq_atoms: (atom * atom) list  (** [(a1, a2) :: _] means [a1 =/= a2] *)
  ; fresh: var list AtomMap.t  (** [a -> [x_1, ..., x_n]] means [a # x_1, ..., a # x_n] *)
  ; subshapes: shape list VarMap.t  (** [x -> [s_1,..., s_n]] means [s_1 < x, ..., s_n < x] *)
  ; shape: shape VarMap.t  (** [x -> s] means [x ~ s] *)
  ; varshapes: var VarMap.t  (** [x -> y] means [x ~ y]*) }

let empty =
  { symbols= []
  ; neq_atoms= []
  ; fresh= AtomMap.empty
  ; subshapes= VarMap.empty
  ; varshapes= VarMap.empty
  ; shape= VarMap.empty }

let merge xs ys =
  let sort = List.sort_uniq compare in
  let merge = List.merge compare in
  merge (sort xs) (sort ys)

let on_subshapes f env = {env with subshapes= f env.subshapes}

let on_shape f env = {env with shape= f env.shape}

let on_varshapes f env = {env with varshapes= f env.varshapes}

let on_symbols f env = {env with symbols= f env.symbols}

let on_fresh f env = {env with fresh= f env.fresh}

let on_neq_atoms f env = {env with neq_atoms= f env.neq_atoms}

let set_fresh fresh env = {env with fresh}

let set_neq_atoms neq_atoms env = {env with neq_atoms}

let set_symbols symbols env = {env with symbols}

let set_varshape x y =
  let rec set x y varshape =
    if x = y then varshape
    else
      match VarMap.find_opt x varshape with
      | None -> VarMap.add x y varshape
      | Some z -> set z y (* if [x -> z] then [z -> y] as well *) $ VarMap.add x y varshape
  in
  on_varshapes (set x y)

let remove_subshapes = on_subshapes % VarMap.remove

let remove_shape = on_shape % VarMap.remove

let rec get_varshape env x =
  match VarMap.find_opt x env.varshapes with
  | Some x' -> get_varshape env x'
  | None -> x

let get_shape env x =
  let x = get_varshape env x in
  VarMap.find_opt x env.shape

let get_shape_def env x =
  let x = get_varshape env x in
  let default = S_Var x in
  Option.value ~default $ get_shape env x

let rec get_subshapes env x =
  match VarMap.find_opt x env.subshapes with
  | Some shapes -> List.map (rebuild_shape env) shapes
  | None -> []

and rebuild_shape env = function
  | S_Var x -> get_shape_def env x
  | S_Atom -> S_Atom
  | S_Lam s -> S_Lam (rebuild_shape env s)
  | S_App (s1, s2) -> S_App (rebuild_shape env s1, rebuild_shape env s2)
  | S_Fun f -> S_Fun f

let rec shape_of_term env = function
  | T_Atom _ -> S_Atom
  | T_Var {symb= x; _} -> S_Var (get_varshape env x)
  | T_Lam (_, t) -> S_Lam (shape_of_term env t)
  | T_App (t1, t2) -> S_App (shape_of_term env t1, shape_of_term env t2)
  | T_Fun f -> S_Fun f

let rec vars_of_shape = function
  | S_Var x -> [x]
  | S_Atom -> []
  | S_Lam s -> vars_of_shape s
  | S_App (s1, s2) -> List.merge compare (vars_of_shape s1) (vars_of_shape s2)
  | S_Fun _ -> []

let is_neq env a1 a2 = List.exists (pair_eq ( = ) (a1, a2)) env.neq_atoms

let is_fresh env a x =
  match AtomMap.find_opt a env.fresh with
  | None -> false
  | Some xs -> List.mem x xs

let is_symbol env x =
  let x = get_varshape env x in
  List.exists (( = ) x % get_varshape env) env.symbols

let rec syntactic_occurs_check x = function
  | S_Var x' -> x' = x
  | S_Lam s -> syntactic_occurs_check x s
  | S_App (s1, s2) -> syntactic_occurs_check x s1 || syntactic_occurs_check x s2
  | S_Atom | S_Fun _ -> false

let rec occurs_check env x t =
  let x = get_varshape env x in
  (*                    x_i occurs syntactically in t                  *)
  (* ---------------------------------------------------------------- *)
  (*  G, [t_1, ..., t_n] < [x_1 ~...~ x ~...~ x_m] ; x ~ t, C |- c  *)
  syntactic_occurs_check x (rebuild_shape env t) || List.exists (occurs_check_subshapes env x) $ vars_of_shape t

and occurs_check_subshapes env x y =
  (*      y occurs syntactically in t       G |- x occurs in t_i       *)
  (* ---------------------------------------------------------------- *)
  (*  G, [t_1, ..., t_n] < [y_1 ~...~ y ~...~ y_m] ; x ~ t, C |- c  *)
  List.exists (occurs_check env x) $ get_subshapes env y

let add_to_list_map update a = function
  | [] -> id
  | xs ->
    update a (function
      | None -> Some xs
      | Some ys -> Some (merge xs ys) )

let add_to_subshapes = on_subshapes %% add_to_list_map VarMap.update

let add_subshape t x env =
  let x = get_varshape env x in
  if occurs_check env x t then None
  else if is_symbol env x then None
  else
    let assms =
      match get_shape env x with
      | Some sx -> [t <: sx]
      | None -> []
    in
    Some (add_to_subshapes x [t] env, assms)

let add_fresh a x = on_fresh $ add_to_list_map AtomMap.update a [x]

let add_neq_atoms a1 a2 = on_neq_atoms $ merge [(a1, a2)]

let add_neq a1 a2 = function
  | _ when a1 = a2 -> None
  | env -> Some (add_neq_atoms a1 a2 env)

let add_symbol t = on_symbols $ merge [t]

let set_var_shape_in_symbols x s env =
  let xs, symbols_without_x = yank x env.symbols in
  (set_symbols symbols_without_x env, if null xs then [] else [symbol s])

let set_var_shape_in_subshapes x s env =
  let subshape_new_shape x_subshape = x_subshape <: s in
  (env, List.map subshape_new_shape $ get_subshapes env x)

let set_var_shape_in_shape x s env =
  match get_shape env x with
  | Some sx -> (env, [s =~: sx])
  | None -> (on_shape (VarMap.add x s) env, [])

let merge_shapes x y env =
  match get_shape env x with
  | Some x_shape -> set_var_shape_in_shape y x_shape env
  | None -> (env, [])

let add_same_shape x y env =
  (*       G; C |- c          x ∈ zs     y ∈ zs    G, [ts] < [zs]; C |- c  *)
  (* ------------------      --------------------------------------------- *)
  (*  G; x ~ x, C |- c               G, [ts] < [zs]; x ~ y, C |- c         *)
  if x = y then Some (env, [])
  else
    let x = get_varshape env x in
    let y = get_varshape env y in
    if x = y then Some (env, [])
    else
      (* G |- x ∈ y G |- y ∈ x *)
      (* --------------------     -------------------- *)
      (*  G; x ~ y, C |- c        G; x ~ y, C |- c   *)
      let x_shape = get_shape_def env x in
      let y_shape = get_shape_def env y in
      if occurs_check env x y_shape || occurs_check env y x_shape then None
      else
        let env, subshape_assms = set_var_shape_in_subshapes x y_shape env in
        let env, shape_assms = merge_shapes x y env in
        let env = set_varshape x y % remove_shape x % remove_subshapes x $ env in
        Some (env, shape_assms @ subshape_assms)

let set_var_shape x s env =
  let x = get_varshape env x in
  match rebuild_shape env s with
  | S_Var y -> add_same_shape x y env
  | s when occurs_check env x s -> None
  | s ->
    let env, symbol_assms = set_var_shape_in_symbols x s env in
    let env, subshape_assms = set_var_shape_in_subshapes x s env in
    let env, shape_assms = set_var_shape_in_shape x s env in
    Some (env, symbol_assms @ shape_assms @ subshape_assms)

let sub_var_in_fresh x t env =
  let sub_in_fresh a xs (fresh, assms) =
    let xs, ys = yank x xs in
    let a_assms = if null xs then [] else [a #: t] in
    (AtomMap.add a ys fresh, a_assms @ assms)
  in
  let fresh, fresh_assms = AtomMap.fold sub_in_fresh env.fresh (AtomMap.empty, []) in
  (set_fresh fresh env, fresh_assms)

let subst_var x t env =
  let s = shape_of_term env t in
  let env, fresh_assms = sub_var_in_fresh x t env in
  on_snd (( @ ) fresh_assms) <$> set_var_shape x s env

let are_same_shape env x1 x2 = x1 = x2 || get_varshape env x1 = get_varshape env x2

let subst_atom a b env =
  let sub_atom_in_neq env =
    let sub c = if c = a then b else c in
    let add_neq env (a1, a2) = env >>= add_neq (sub a1) (sub a2) in
    List.fold_left add_neq (some $ set_neq_atoms [] env) env.neq_atoms
  and sub_atom_in_fresh env =
    match AtomMap.find_opt a env.fresh with
    | None -> env
    | Some xs -> on_fresh (add_to_list_map AtomMap.update b xs % AtomMap.remove a) env
  in
  sub_atom_in_neq $ sub_atom_in_fresh env

let set_var_symbol x env =
  let env = add_symbol x env in
  let assms =
    match get_shape env x with
    | Some s -> [symbol s]
    | None -> []
  in
  (env, assms)

let add_symbol x env =
  let x = get_varshape env x in
  match get_subshapes env x with
  | [] -> Some (set_var_symbol x env)
  | _ -> None (* no term subshapes symbols *)
