open Types
open Common
open Substitution

type atom_assumption =
  | A_Fresh    of atom * var
  | A_Neq      of atom * atom
  | A_Shape    of var * var
  | A_Subshape of term * var

type t = atom_assumption list

let empty = []

let add_fresh gamma a x = A_Fresh (a, x) :: gamma

let add_neq gamma a a' = if a = a' then None else Some (A_Neq (a, a') :: gamma)

let add_same_shape gamma x y =
  (* TODO: this function should utilise some kind of union-find, this trivial implementation won't
     work in general case *)
  if x = y then gamma else A_Shape (x, y) :: gamma

let add_subshape gamma t x =
  (* TODO: this function should utilise some kind of union-find, this trivial implementation won't
     work in general case *)
  A_Subshape (t, x) :: gamma

let is_neq gamma a1 a2 =
  List.exists
    (function
      | A_Neq (b1, b2) -> pair_eq (a1, a2) (b1, b2)
      | _              -> false )
    gamma

let is_fresh gamma a x = List.mem (A_Fresh (a, x)) gamma

let add_constr gamma = function
  | A_Neq (a1, a2)    -> add_neq gamma a1 a2
  | A_Fresh (a, v)    -> Some (add_fresh gamma a v)
  | A_Shape (x, y)    -> Some (add_same_shape gamma x y)
  | A_Subshape (t, x) -> Some (add_subshape gamma t x)

let subst_atom_constr a b = function
  | A_Neq (a1, a2)                  -> A_Neq (subst a b a1, subst a b a2)
  | A_Fresh (c, v)                  -> A_Fresh (subst a b c, v)
  | (A_Shape _ | A_Subshape _) as c -> c

let subst_atom gamma a b =
  List.fold_left
    (fun env constr -> Option.bind env (flip add_constr $ subst_atom_constr a b constr))
    (Some empty) gamma

let subst_var gamma x t =
  List.fold_left
    (fun (env, assmpts) -> function
      | A_Fresh (a, x') when x = x' -> (env, (a #: t) :: assmpts)
      | A_Shape (x1, x2) when x = x1 -> (env, (t =~: var x2) :: assmpts)
      | A_Shape (x1, x2) when x = x2 -> (env, (t =~: var x1) :: assmpts)
      | A_Subshape (t', x') -> (env, subst_var_in_constr x t (t' <: var x') :: assmpts)
      | ac -> (ac :: env, assmpts) )
    (empty, []) gamma

let string_of_atom_assumption assmpt =
  Printing.string_of_constr
    ( match assmpt with
    | A_Fresh (a, v)    -> C_Fresh (a, T_Var {perm= []; symb= v})
    | A_Neq (a, b)      -> C_AtomNeq (a, {perm= []; symb= b})
    | A_Shape (x, y)    -> C_Shape (var x, var y)
    | A_Subshape (t, x) -> C_Subshape (t, var x) )

let are_same_shape gamma x1 x2 =
  (* TODO: this function should utilise some kind of union-find, this trivial implementation won't
     work in general case *)
  x1 = x2
  || List.exists
       (function
         | A_Shape (y1, y2) -> pair_eq (x1, x2) (y1, y2)
         | _                -> false )
       gamma

let get_subshapes gamma x =
  (* TODO: this function should utilise some kind of union-find, this trivial implementation won't
     work in general case *)
  List.filter_map
    (function
      | A_Subshape (t, y) when x = y -> Some t
      | _ -> None )
    gamma

let string_of = Printing.string_of_list string_of_atom_assumption ~sep:", "
