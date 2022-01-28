open Types
open Common
open Solver
open Permutation
open Printing
open KindChecker
open KindCheckerEnv

let print_result expr res = print_endline $ " ⊢ " ^ expr ^ "\t" ^ if res then "✅" else "❌"

let print_solver c = print_result $ string_of_constr c $ Solver.solve c

let print_subkind_solver (k1, k2) =
  print_result
  $ string_of_kind k1 ^ " ≤ " ^ string_of_kind k2
  $ KindChecker.subkind KindCheckerEnv.empty k1 k2

let print_kind_solver (formula, kind) =
  print_result
  $ string_of_formula formula ^ " : " ^ string_of_kind kind
  $ KindChecker.check kind formula

let examples =
  let a_ = A "a" and b_ = A "b" and c_ = A "c" in
  let a = {perm= []; symb= a_} and b = {perm= []; symb= b_} and c = {perm= []; symb= c_} in
  let pi = [(b, c)] in
  let x = Var {perm= []; symb= V "x"} in
  [ x =: x
  ; a_ #: (Lam (a, Atom a))
  ; a_ #: (permute_term [] (Lam (b, Atom b)))
  ; a_ #: (permute_term pi (Lam (b, Atom b)))
  ; App (Atom a, Atom b) =: App (Atom a, Atom b)
  ; Lam (a, Atom a) =: Lam (b, Atom b) ]

let subkind_examples = [(Prop, Prop); (ForallTerm (V "x", Prop), ForallTerm (V "y", Prop))]

let kind_examples = [(F_Bot, Prop)]

let _ = List.iter print_solver examples

let _ = print_newline ()

let _ = List.iter print_subkind_solver subkind_examples

let _ = print_newline ()

let _ = List.iter print_kind_solver kind_examples
