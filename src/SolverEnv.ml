open Types
open Common
open Substitution

(** Here one would expect constructors like [A_Shape of var * var] ([x_1 =~ x_2]) and [A_Subshape of
    term * var], ([t <: x]), but we decided it is best to keep those assumptions in groupings like
    [[t_1, ..., t_n] <: [x_1 ~...~ x_m]], where each [t_i] subshapes every [x_j], keeping
    _abstraction classes_ together *)
type atom_assumption =
  | A_Fresh of atom * var
  | A_Neq   of atom * atom
  | A_Shape of term list * var list

type t = atom_assumption list

let empty = []

let add_fresh gamma a x = A_Fresh (a, x) :: gamma

let add_neq gamma a1 a2 = if a1 = a2 then None else Some (A_Neq (a1, a2) :: gamma)

let find_shapes gamma x =
  match
    List.partition
      (function
        | A_Shape (_, vs) -> List.mem x vs
        | _               -> false )
      gamma
  with
  | [], gamma                 -> ([], [x], gamma)
  | [A_Shape (ts, vs)], gamma -> (ts, vs, gamma)
  | _                         -> assert false

let syntactic_occurs_check_many xs t = List.exists (flip syntactic_occurs_check t) xs

let rec occurs_check gamma x t =
  let _, xs, gamma = find_shapes gamma x in
  (*                    x_i occurs syntatically in t                  *)
  (* ---------------------------------------------------------------- *)
  (*  G, [t_1, ..., t_n] <: [x_1 ~...~ x ~...~ x_m] ; x =~: t, C |- c  *)
  syntactic_occurs_check_many xs t
  ||
  let occurs_check_subshapes y =
    (*      y occurs syntatically in t       G |- x occurs in t_i       *)
    (* ---------------------------------------------------------------- *)
    (*  G, [t_1, ..., t_n] <: [y_1 ~...~ y ~...~ y_m] ; x =~: t, C |- c  *)
    let ts, _, gamma = find_shapes gamma y in
    List.exists (occurs_check gamma x) ts
  in
  List.exists occurs_check_subshapes $ free_vars_of_term t

let add_same_shape gamma x y =
  (*       G; C |- c           x ∈ xs     y ∈ zs    G, [ts] <: [zs]; C |- c  *)
  (* --------------------     ---------------------------------------------- *)
  (*  G; x =~: x, C |- c              G, [ts] <: [zs]; x =~: y, C |- c         *)
  if
    x = y
    || List.exists
         (function
           | A_Shape (_, vs) -> List.mem x vs && List.mem y vs
           | _               -> false )
         gamma
  then Some gamma
    (*    G |- x ∈ y                  G |- y ∈ x     *)
    (* --------------------     -------------------- *)
    (*  G; x =~: y, C |- c        G; x =~: y, C |- c   *)
  else if occurs_check gamma x (var y) || occurs_check gamma y (var x) then None
  else
    (*  x ∈ xs     G |- x ∉ y     y ∈ ys     G |- y ∉ x  *)
    (*        G, [ts @ ss] <: [xs @ ys]; C |- c          *)
    (* ------------------------------------------------- *)
    (*   G, [ts] <: [xs], [ss] <: [ys]; x =~: y, C |- c   *)
    let x_shapes, x_vars, gamma = find_shapes gamma x in
    let y_shapes, y_vars, gamma = find_shapes gamma y in
    Option.some $ A_Shape (x_shapes @ y_shapes, x_vars @ y_vars) :: gamma

let add_subshape gamma t x =
  if occurs_check gamma x t then None
  else
    let ts, xs, gamma = find_shapes gamma x in
    Some (A_Shape (t :: ts, xs) :: gamma)

let is_neq gamma a1 a2 =
  List.exists
    (function
      | A_Neq (b1, b2) -> pair_eq (a1, a2) (b1, b2)
      | _              -> false )
    gamma

let is_fresh gamma a x = List.mem (A_Fresh (a, x)) gamma

let subst_atom gamma a b =
  let subst_atom_constr a b = function
    | A_Neq (a1, a2) -> A_Neq (subst a b a1, subst a b a2)
    | A_Fresh (c, v) -> A_Fresh (subst a b c, v)
    | A_Shape _ as c (* Atoms do not affect shape *) -> c
  in
  let add_constr constr gamma =
    match subst_atom_constr a b constr with
    | A_Neq (a1, a2) -> add_neq gamma a1 a2
    | A_Fresh (a, v) -> Some (add_fresh gamma a v)
    | A_Shape _ as a (* Atoms do not affect shape *) -> Some (a :: gamma)
  in
  List.fold_left (fun env constr -> env >>= add_constr constr) (Some empty) gamma

let subst_var gamma x t =
  if occurs_check gamma x t then None
  else
    (*  G{t/x}, [t_1, ..., t_n] <: [x_1 ~...~ x_m] ;                       *)
    (*           t_1 <: t, ..., t_n <: t, x_1 =~: t, ..., x_m =~: t, C |- c  *)
    (* ------------------------------------------------------------------- *)
    (*     (G, [t_1, ..., t_n] <: [x_1 ~...~ x ~...~ x_m]){t/x} ; C |- c   *)
    let ts, xs, gamma = find_shapes gamma x in
    let assms = List.map (fun t' -> t' <: t) ts in
    let gamma, assms =
      match List.filter (fun x' -> x' != x) xs with
      | [] -> (gamma, assms)
      | xs -> (A_Shape (ts, xs) :: gamma, List.map (fun x' -> var x' =~: t) xs @ assms)
    in
    Option.some
    $ List.fold_left
        (fun (env, assms) -> function
          | A_Fresh (a, x') when x = x' -> (env, (a #: t) :: assms)
          (* as we occurs_checked x with t is is safe to just subst*)
          | A_Shape (ts, xs) -> (A_Shape (List.map (subst_var_in_term x t) ts, xs) :: env, assms)
          | (A_Fresh _ | A_Neq _) as ac -> (ac :: env, assms) )
        (empty, assms) gamma

let string_of_atom_assumption = function
  | A_Fresh (a, v)   -> Printing.string_of_constr $ C_Fresh (a, T_Var {perm= []; symb= v})
  | A_Neq (a, b)     -> Printing.string_of_constr $ C_AtomNeq (a, {perm= []; symb= b})
  | A_Shape (ts, xs) ->
      Printing.string_of_list Printing.string_of_term ts
      ^ " <: "
      ^ Printing.string_of_list (Printing.string_of_term % var) xs

let are_same_shape gamma x1 x2 =
  x1 = x2
  || List.exists
       (function
         | A_Shape (_, xs) -> List.mem x1 xs && List.mem x2 xs
         | _               -> false )
       gamma

let get_shapes gamma x =
  match
    List.find_opt
      (function
        | A_Shape (_ts, xs) -> List.mem x xs
        | _                 -> false )
      gamma
  with
  | Some (A_Shape (_ts, xs)) -> xs
  | None                     -> [x]
  | _                        -> assert false

let get_subshapes gamma x =
  List.concat
  $ List.filter_map
      (function
        | A_Shape (ts, xs) when List.mem x xs -> Some ts
        | _ -> None )
      gamma

let string_of = Printing.string_of_list string_of_atom_assumption ~sep:", "
