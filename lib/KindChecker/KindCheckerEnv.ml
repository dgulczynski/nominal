open Types
open Common

type kind_assumption =
  | Constr    of constr
  | BoundVar  of var * var
  | BoundAtom of atom * atom
  | BoundFVar of string * fvar * kind

type t = kind_assumption list

let empty = []

let map_var gamma x y = BoundVar (x, y) :: gamma

let map_atom gamma a b = BoundAtom (a, b) :: gamma

let find_var gamma x =
  hd_opt
  $ List.filter_map
      (function
        | BoundVar (x', y) when x = x' -> Some y
        | _ -> None )
      gamma

let find_atom gamma a =
  hd_opt
  $ List.filter_map
      (function
        | BoundAtom (a', b) when a = a' -> Some b
        | _ -> None )
      gamma

let add_constr gamma c = Constr c :: gamma

let mem_constr gamma c = List.mem (Constr c) gamma

let constraints_of =
  List.filter_map (function
    | Constr c -> Some c
    | _        -> None )

let string_of_kind_assumption = function
  | Constr c                 -> Printing.string_of_constr c
  | BoundVar (x, y)          -> Printing.string_of_var_arg x ^ "↦" ^ Printing.string_of_var_arg y
  | BoundAtom (a, b)         -> Printing.string_of_atom_arg a ^ "↦" ^ Printing.string_of_atom_arg b
  | BoundFVar (x_name, _, k) -> x_name ^ "↦" ^ Printing.string_of_kind k

let string_of = Printing.string_of_list string_of_kind_assumption ~sep:", "

let map_fvar gamma x_name x k = BoundFVar (x_name, x, k) :: gamma

let find_fvar gamma x =
  hd_opt
  $ List.filter_map
      (function
        | BoundFVar (_, x', k) when x = x' -> Some k
        | _ -> None )
      gamma
