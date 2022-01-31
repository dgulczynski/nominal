open Types
open Common

let fresh_generator prefix =
  let counter = ref 0 in
  fun () ->
    counter := !counter + 1 ;
    prefix ^ string_of_int !counter

let fresh_var =
  let generate = fresh_generator "_x" in
  fun () -> V (generate ())

let fresh_atom =
  let generate = fresh_generator "_a" in
  fun () -> A (generate ())

type kind_assumption = Constr of constr | BoundVar of var * var | BoundAtom of atom * atom

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
  | Constr c         -> Printing.string_of_constr c
  | BoundVar (x, y)  -> Printing.string_of_var_arg x ^ "↦" ^ Printing.string_of_var_arg y
  | BoundAtom (a, b) -> Printing.string_of_atom_arg a ^ "↦" ^ Printing.string_of_atom_arg b

let string_of = Printing.string_of_list string_of_kind_assumption ~sep:", "
