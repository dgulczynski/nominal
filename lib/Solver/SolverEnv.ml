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

(* x_Δ := y_Δ  when Δ.varshape(x) = y *)
(* x_Δ := x    when Δ.varshape(x) = ∅ *)
let rec get_varshape env x =
  match VarMap.find_opt x env.varshapes with
  | Some x' -> get_varshape env x'
  | None -> x

(* (x ~ s) ∈ Δ := Δ.shape(x_Δ) = s *)
let get_shape env x =
  let x = get_varshape env x in
  VarMap.find_opt x env.shape

(* Δ|x| := Δ|y| when Δ.varshape(x) = y *)
(* Δ|x| := s    when Δ.shape(x) = s    *)
(* Δ|x| := x    otherwise              *)
let get_shape_def env x =
  let x = get_varshape env x in
  let default = S_Var x in
  Option.value ~default $ get_shape env x

(* (s < x) ∈ Δ := s ∈ Δ.subshape(x_Δ) *)
let rec get_subshapes env x =
  match VarMap.find_opt x env.subshapes with
  | Some shapes -> List.map (rebuild_shape env) shapes
  | None -> []

(* Δ|_|     := _           *)
(* Δ|_.s|   := _.Δ|s|      *)
(* Δ|s1 s2| := Δ|s1| Δ|s2| *)
(* Δ|f|     := f           *)
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

(* (a1 =/= a2) ∈ Δ := (a1 =/= a2) ∈ Δ.neq_atoms *)
let is_neq env a1 a2 = List.exists (pair_eq ( = ) (a1, a2)) env.neq_atoms

(* (a # x) ∈ Δ := x ∈ Δ.fresh(a) *)
let is_fresh env a x =
  match AtomMap.find_opt a env.fresh with
  | None -> false
  | Some xs -> List.mem x xs

(* (symbol x) ∈ Δ := x_Δ ∈ Δ.symbols *)
let is_symbol env x =
  let x = get_varshape env x in
  List.exists (( = ) x % get_varshape env) env.symbols

let rec syntactic_occurs_check x = function
  | S_Var x' -> x' = x
  | S_Lam s -> syntactic_occurs_check x s
  | S_App (s1, s2) -> syntactic_occurs_check x s1 || syntactic_occurs_check x s2
  | S_Atom | S_Fun _ -> false

let rec occurs_check env x s =
  (*  x_Δ occurs syntactically in Δ|s|  *)
  (* ---------------------------------- *)
  (*          Δ |= x occurs in s        *)
  let x = get_varshape env x in
  let s = rebuild_shape env s in
  syntactic_occurs_check x s || List.exists (occurs_check_subshapes env x) $ vars_of_shape s

and occurs_check_subshapes env x y =
  (*  y occurs syntactically in Δ|s| *)
  (*        s' ∈ Δ.subshapes(y)      *)
  (*        Δ |= x occurs in s'      *)
  (* ------------------------------- *)
  (*        Δ |= x occurs in s       *)
  List.exists (occurs_check env x) $ get_subshapes env y

let add_to_list_map update a = function
  | [] -> id
  | xs ->
    update a (function
      | None -> Some xs
      | Some ys -> Some (merge xs ys) )

let add_to_subshapes = on_subshapes %% add_to_list_map VarMap.update

(* (s < x) ∪ Δ := ↯                                               when Δ |= x occurs in s *)
(* (s < x) ∪ Δ := ↯                                               when x_Δ ∈ Δ.symbols    *)
(* (s < x) ∪ Δ := Δ[subshapes(x_Δ) += s]                          when Δ.shape(x_Δ) = ∅   *)
(* (s < x) ∪ Δ := Δ[subshapes(x_Δ) += s, assumptions += (s < s')] when Δ.shape(x_Δ) = s'  *)
let add_subshape s x env =
  let x = get_varshape env x in
  if occurs_check env x s then None
  else if is_symbol env x then None
  else
    let assms =
      match get_shape env x with
      | Some sx ->
        [s <: sx]
        (* Note: this should not be thought as  adding a new constraint to solver    *)
        (* but rather a way of finding the actual form of the (s < x) to be (s < sx) *)
      | None -> []
    in
    Some (add_to_subshapes x [s] env, assms)

(* (a # x) ∪ Δ := Δ[fresh(a) += x] *)
let add_fresh a x = on_fresh $ add_to_list_map AtomMap.update a [x]

let add_neq_atoms a1 a2 = on_neq_atoms $ merge [(a1, a2)]

(* (a =/= a) ∪ Δ := ↯                      *)
(* (a =/= b) ∪ Δ := Δ[neq_atoms += (a =/= b)] *)
let add_neq a1 a2 = function
  | _ when a1 = a2 -> None
  | env -> Some (add_neq_atoms a1 a2 env)

let add_symbol t = on_symbols $ merge [t]

(* Δ.symbols{x ~> s} := Δ[symbols -= {x}, assumptions += (symbol s)] when x ∈ Δ.symbols *)
(* Δ.symbols{x ~> s} := Δ                                            when x ∉ Δ.symbols *)
let set_var_shape_in_symbols x s env =
  let xs, symbols_without_x = yank x env.symbols in
  (set_symbols symbols_without_x env, if null xs then [] else [symbol s])

(* Δ.subshapes{x ~> s} := Δ[assumptions += Δ.subshapes(x).map(fun s_x -> s_x < s)] *)
let set_var_shape_in_subshapes x s env =
  let subshape_new_shape x_subshape = x_subshape <: s in
  (env, List.map subshape_new_shape $ get_subshapes env x)

(* Δ.shapes{x ~> s} := Δ[assumptions += (s ~ s')] when Δ.shape(x) = s' *)
(* Δ.shapes{x ~> s} := Δ[shapes[x -> s]]          when Δ.shape(x) = ∅ *)
let set_var_shape_in_shape x s env =
  match get_shape env x with
  | Some sx -> (env, [s =~: sx])
  | None -> (on_shape (VarMap.add x s) env, [])

(* Δ.transfer_shape(x ~> y) := Δ.shapes{y ~> s} when Δ.shape(x) = s *)
(* Δ.transfer_shape(x ~> y) := Δ                when Δ.shape(x) = ∅ *)
let transfer_shape x y env =
  match get_shape env x with
  | Some x_shape -> set_var_shape_in_shape y x_shape env
  | None -> (env, [])

(* (x ~ y) ∪ Δ := Δ when x_Δ = y_Δ             *)
(* (x ~ y) ∪ Δ := Δ when Δ|x| = Δ|y|           *)
(* (x ~ y) ∪ Δ := ↯ when x_Δ occurs in Δ|y|    *)
(* (x ~ y) ∪ Δ := ↯ when y_Δ occurs in Δ|x|    *)
(* (x ~ y) ∪ Δ := Δ' otherwise                 *)
(* where Δ' = Δ.symbols{x_Δ ~> Δ|y|}          *)
(*             .subshapes{x_Δ ~> Δ|y|}        *)
(*             .transfer_shape(x_Δ ~> y_Δ)    *)
(*             [ shape.remove(x_Δ)            *)
(*             , subshape.remove(x_Δ)         *)
(*             , varshape[x_Δ -> y_Δ]         *)
(*             ]                              *)
let add_same_shape x y env =
  if x = y then Some (env, [])
  else
    let x = get_varshape env x in
    let y = get_varshape env y in
    if x = y then Some (env, [])
    else
      let x_shape = get_shape_def env x in
      let y_shape = get_shape_def env y in
      if occurs_check env x y_shape || occurs_check env y x_shape then None
      else
        let env, symbol_assms = set_var_shape_in_symbols x y_shape env in
        let env, subshape_assms = set_var_shape_in_subshapes x y_shape env in
        let env, shape_assms = transfer_shape x y env in
        let env = set_varshape x y % remove_shape x % remove_subshapes x $ env in
        Some (env, symbol_assms @ shape_assms @ subshape_assms)

(* (x ~ s) ∪ Δ := ↯ when x occurs in s  *)
(* (x ~ s) ∪ Δ := Δ' otherwise          *)
(* where Δ' = Δ.symbols{x_Δ ~> Δ|s|}   *)
(*             .subshapes{x_Δ ~> Δ|s|} *)
(*             .shapes{x_Δ ~> Δ|s|}    *)
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

(* Δ.fresh{x -> t} := (U_{(a # xs) ∈ Δ.fresh | x ∈ xs} (a # t)) ∪ Δ[fresh.map(fun (a # xs) -> (a # xs - {x})] *)
let sub_var_in_fresh x t env =
  let sub_in_fresh a xs (fresh, assms) =
    let xs, ys = yank x xs in
    let a_assms = if null xs then [] else [a #: t] in
    (AtomMap.add a ys fresh, a_assms @ assms)
  in
  let fresh, fresh_assms = AtomMap.fold sub_in_fresh env.fresh (AtomMap.empty, []) in
  (set_fresh fresh env, fresh_assms)

(* Δ {x -> t} := (x ~ Δ||t||) ∪ Δ.fresh{x -> t} *)
let subst_var x t env =
  let s = shape_of_term env t in
  let env, fresh_assms = sub_var_in_fresh x t env in
  on_snd (List.append fresh_assms) <$> set_var_shape x s env

(* (x1 ~ x2) ∈ Δ := x1_Δ := x2_Δ*)
let are_same_shape env x1 x2 = x1 = x2 || get_varshape env x1 = get_varshape env x2

(* Δ.neq_atoms {a -> b} := (U_{(a1 =/= a2) in Δ.neq_atoms} (a1{a -> b} =/= a2{a -> b})) ∪ Δ[neq_atoms = ∅] *)
let sub_atom_in_neq a b env =
  let sub c = if c = a then b else c in
  let add_neq env (a1, a2) = env >>= add_neq (sub a1) (sub a2) in
  List.fold_left add_neq (some $ set_neq_atoms [] env) env.neq_atoms

(* Δ.fresh {a -> b} := Δ[fresh.remove(a).(b) += Δ.fresh(a)] *)
let sub_atom_in_fresh a b env =
  match AtomMap.find_opt a env.fresh with
  | None -> env
  | Some xs -> on_fresh (add_to_list_map AtomMap.update b xs % AtomMap.remove a) env

(* Δ {a -> b} := Δ.fresh{a -> b}.neq_atoms{a -> b} *)
let subst_atom a b = sub_atom_in_neq a b % sub_atom_in_fresh a b

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
