open Types
open Prelude

type kind_assm =
  | Constr of constr
  | BoundVar of var * var
  | BoundAtom of atom * atom
  | BoundFVar of string * fvar * kind

type t = kind_assm list

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
    | _ -> None )

let map_fvar gamma x_name x k = BoundFVar (x_name, x, k) :: gamma

let find_fvar gamma x =
  hd_opt
  $ List.filter_map
      (function
        | BoundFVar (_, x', k) when x = x' -> Some k
        | _ -> None )
      gamma
