open Types
open Common
open Substitution

type atom_assumption = A_Fresh of atom * var | A_Neq of atom * atom

type t = atom_assumption list

let empty = []

let add_fresh gamma a x = A_Fresh (a, x) :: gamma

let add_neq gamma a a' = if a = a' then None else Some (A_Neq (a, a') :: gamma)

let is_neq gamma a1 a2 =
  List.exists
    (function
      | A_Neq (b1, b2) -> (b1 = a1 && b2 = a2) || (b1 = a2 && b2 = a1)
      | A_Fresh _      -> false )
    gamma

let is_fresh gamma a x = List.mem (A_Fresh (a, x)) gamma

let add_constr gamma = function
  | A_Neq (a1, a2) -> add_neq gamma a1 a2
  | A_Fresh (a, v) -> Some (add_fresh gamma a v)

let subst_atom_constr a b = function
  | A_Neq (a1, a2) -> A_Neq (subst a b a1, subst a b a2)
  | A_Fresh (c, v) -> A_Fresh (subst a b c, v)

let subst_atom gamma a b =
  List.fold_left
    (fun env constr -> Option.bind env (flip add_constr $ subst_atom_constr a b constr))
    (Some empty) gamma

let subst_var gamma x t =
  List.fold_left
    (fun (env, assmpts) -> function
      | A_Fresh (a, x') when x = x' -> (env, (a #: t) :: assmpts)
      | c -> (c :: env, assmpts) )
    (empty, []) gamma

let string_of_atom_assumption assmpt =
  Printing.string_of_constr
    ( match assmpt with
    | A_Fresh (a, v) -> C_Fresh (a, T_Var {perm= []; symb= v})
    | A_Neq (a, b)   -> C_AtomNeq (a, {perm= []; symb= b}) )

let string_of = Printing.string_of_list string_of_atom_assumption ~sep:", "
