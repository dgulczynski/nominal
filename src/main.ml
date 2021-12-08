open Types
open Common
open Solver
open Printing

let print_solver c =
  let b = Solver.solve c in
  print_endline $ " |- " ^ string_of_constr c ^ " => " ^ if b then "True" else "False"

let examples =
  let a_ = A "a" and b_ = A "b" in
  let a = Just a_ and b = Just b_ in
  let x = Var (Just (V "x")) in
  [ x =: x
  ; a_ #: (Lam (a, Atom a))
  ; a_ #: (Lam (b, Atom b))
  ; App (Atom a, Atom b) =: App (Atom a, Atom b) ]

let _ = List.iter print_solver examples
