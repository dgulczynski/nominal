open Types
open Common
open Substitution
open Utils

type atom_assumption =
  | A_Fresh of atom * var
  | A_Neq of atom * atom
      (** Here one would expect constructors like [A_Shape of var * var] ([x_1 =~ x_2])
          and [A_Subshape of term * var], ([t < x]),
          but we decided it is best to keep those assumptions
          in groupings like [[t_1, ..., t_n] < [x_1 ~...~ x_m]],
          where each [t_i] subshapes every [x_j],
          keeping _abstraction classes_ together *)
  | A_Shape of term list * var list
  | A_Symbol of var

type t = atom_assumption list

let empty = []

let add_fresh env a x = A_Fresh (a, x) :: env

let add_neq env a1 a2 = if a1 = a2 then None else Some (A_Neq (a1, a2) :: env)

let find_shapes env x =
  match
    List.partition
      (function
        | A_Shape (_, vs) -> List.mem x vs
        | _ -> false )
      env
  with
  | [], env -> ([], [x], env)
  | [A_Shape (ts, vs)], env -> (ts, vs, env)
  | _ -> assert false

let syntactic_occurs_check_many xs t = List.exists (flip syntactic_occurs_check t) xs

let rec occurs_check env x t =
  let _, xs, env = find_shapes env x in
  (*                    x_i occurs syntatically in t                  *)
  (* ---------------------------------------------------------------- *)
  (*  G, [t_1, ..., t_n] < [x_1 ~...~ x ~...~ x_m] ; x ~ t, C |- c  *)
  syntactic_occurs_check_many xs t
  ||
  let occurs_check_subshapes y =
    (*      y occurs syntatically in t       G |- x occurs in t_i       *)
    (* ---------------------------------------------------------------- *)
    (*  G, [t_1, ..., t_n] < [y_1 ~...~ y ~...~ y_m] ; x ~ t, C |- c  *)
    let ts, _, env = find_shapes env y in
    List.exists (occurs_check env x) ts
  in
  List.exists occurs_check_subshapes $ free_vars_of_term t

let add_same_shape env x y =
  (*       G; C |- c          x ∈ zs     y ∈ zs    G, [ts] < [zs]; C |- c  *)
  (* ------------------      --------------------------------------------- *)
  (*  G; x ~ x, C |- c               G, [ts] < [zs]; x ~ y, C |- c         *)
  if
    x = y
    || List.exists
         (function
           | A_Shape (_, vs) -> List.mem x vs && List.mem y vs
           | _ -> false )
         env
  then Some env
    (*    G |- x ∈ y                  G |- y ∈ x     *)
    (* --------------------     -------------------- *)
    (*  G; x ~ y, C |- c        G; x ~ y, C |- c   *)
  else if occurs_check env x (var y) || occurs_check env y (var x) then None
  else
    (*  x ∈ xs     G |- x ∉ y    y ∈ ys     G |- y ∉ x  *)
    (*         G, [ts @ ss] < [xs @ ys]; C |- c          *)
    (* ------------------------------------------------- *)
    (*     G, [ts] < [xs], [ss] < [ys]; x ~ y, C |- c    *)
    let x_shapes, x_vars, env = find_shapes env x in
    let y_shapes, y_vars, env = find_shapes env y in
    Option.some $ A_Shape (x_shapes @ y_shapes, x_vars @ y_vars) :: env

let add_subshape env t x =
  if occurs_check env x t then None
  else
    let ts, xs, env = find_shapes env x in
    Some (A_Shape (t :: ts, xs) :: env)

let is_neq env a1 a2 =
  List.exists
    (function
      | A_Neq (b1, b2) -> pair_eq ( = ) (a1, a2) (b1, b2)
      | _ -> false )
    env

let is_fresh env a x = List.mem (A_Fresh (a, x)) env

let subst_atom env a b =
  let subst_atom_constr a b =
    let sub a' = if a = a' then b else a' in
    function
    | A_Neq (a1, a2) -> A_Neq (sub a1, sub a2)
    | A_Fresh (c, v) -> A_Fresh (sub c, v)
    | A_Shape _ as c (* Atoms do not affect shape *) -> c
    | A_Symbol _ as c (* Atoms do not affect symbols *) -> c
  in
  let add_constr constr env =
    match subst_atom_constr a b constr with
    | A_Neq (a1, a2) -> add_neq env a1 a2
    | A_Fresh (a, v) -> Some (add_fresh env a v)
    | A_Shape _ as a (* Atoms do not affect shape *) -> Some (a :: env)
    | A_Symbol _ as a (* Atoms do not affect symbols *) -> Some (a :: env)
  in
  List.fold_left (fun env constr -> env >>= add_constr constr) (Some empty) env

let subst_var env x t =
  if occurs_check env x t then None
  else
    (*  G{t/x}, [t_1, ..., t_n] < [x_1 ~...~ x_m] ;                       *)
    (*           t_1 < t, ..., t_n < t, x_1 ~ t, ..., x_m ~ t, C |- c  *)
    (* ------------------------------------------------------------------- *)
    (*     (G, [t_1, ..., t_n] < [x_1 ~...~ x ~...~ x_m]){t/x} ; C |- c   *)
    let ts, xs, env = find_shapes env x in
    (* Here from [G |- x doesn't occur in t] we know that [G |- x doesn't occur in t_i] *)
    (* So the [t_i < t] is not needed? *)
    let assms = List.map (fun t_i -> t_i <: t) ts in
    let env, assms =
      match List.filter (fun x' -> x' <> x) xs with
      | [] -> (env, assms)
      | xs -> (A_Shape (ts, xs) :: env, List.map (fun x' -> var x' =~: t) xs @ assms)
    in
    Option.some
    $ List.fold_left
        (fun (env, assms) -> function
          | A_Fresh (a, x') when x = x' -> (env, (a #: t) :: assms)
          (* as we occurs_checked x with t is is safe to just subst *)
          | A_Shape (ts, xs) -> (A_Shape (List.map (subst_var_in_term x t) ts, xs) :: env, assms)
          | A_Symbol x' when List.mem x' xs -> (env, symbol t :: assms)
          | (A_Fresh _ | A_Neq _ | A_Symbol _) as a -> (a :: env, assms) )
        (empty, assms) env

let string_of_atom_assumption = function
  | A_Fresh (a, v) -> Printing.string_of_constr $ C_Fresh (a, T_Var {perm= []; symb= v})
  | A_Neq (a, b) -> Printing.string_of_constr $ C_AtomNeq (a, {perm= []; symb= b})
  | A_Shape (ts, xs) ->
    Printing.string_of_list Printing.string_of_term ts
    ^ " < "
    ^ Printing.string_of_list (Printing.string_of_term % var) xs
  | A_Symbol x -> Printing.string_of_constr $ C_Symbol (var x)

let are_same_shape env x1 x2 =
  x1 = x2
  || List.exists
       (function
         | A_Shape (_, xs) -> List.mem x1 xs && List.mem x2 xs
         | _ -> false )
       env

let get_shapes env x =
  match
    List.find_opt
      (function
        | A_Shape (_ts, xs) -> List.mem x xs
        | _ -> false )
      env
  with
  | Some (A_Shape (_ts, xs)) -> xs
  | None -> [x]
  | _ -> assert false

let get_subshapes env x =
  List.concat
  $ List.filter_map
      (function
        | A_Shape (ts, xs) when List.mem x xs -> Some ts
        | _ -> None )
      env

let add_symbol env x =
  match get_subshapes env x with
  | [] -> Some (A_Symbol x :: env)
  | _ -> (* no term subshapes symbols *) None

let is_symbol env x =
  let xs = get_shapes env x in
  let find_symbol = function
    | A_Symbol y -> List.mem y xs
    | _ -> false
  in
  List.exists find_symbol env

let string_of = Printing.string_of_list' ~sep:", " string_of_atom_assumption
