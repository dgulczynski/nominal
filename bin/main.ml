open Nominal
open Types
open Common
open KindChecker
open Permutation
open Printing
open Solver

let print_result expr res = print_endline $ " ⊢ " ^ expr ^ "\t" ^ if res then "✅" else "❌"

let print_solver c = print_result $ string_of_constr c $ solve c

let print_subkind_solver (k1, k2) =
  print_result $ string_of_kind k1 ^ " ≤ " ^ string_of_kind k2 $ (k1 <=: k2)

let print_kind_solver (formula, kind) =
  print_result $ string_of_formula formula ^ " : " ^ string_of_kind kind $ formula -: kind

let examples =
  let a_ = A "a" and b_ = A "b" and c_ = A "c" in
  let a = {perm= []; symb= a_} and b = {perm= []; symb= b_} and c = {perm= []; symb= c_} in
  let pi = [(b, c)] in
  let x = T_Var {perm= []; symb= V "x"} in
  [ x =: x
  ; a_ #: (T_Lam (a, T_Atom a))
  ; a_ #: (permute_term [] (T_Lam (b, T_Atom b)))
  ; a_ #: (permute_term pi (T_Lam (b, T_Atom b)))
  ; T_App (T_Atom a, T_Atom b) =: T_App (T_Atom a, T_Atom b)
  ; T_Lam (a, T_Atom a) =: T_Lam (b, T_Atom b)
  ; T_Lam (a, T_Atom a) =~: T_Lam (b, T_Atom b)
  ; T_Atom a <: T_Lam (b, T_Atom b) ]

let subkind_examples =
  [(K_Prop, K_Prop); (K_ForallTerm (V "x", K_Prop), K_ForallTerm (V "y", K_Prop))]

let kind_examples = [(F_Bot, K_Prop)]

let _ = List.iter print_solver examples

let _ = print_newline ()

let _ = List.iter print_subkind_solver subkind_examples

let _ = print_newline ()

let _ = List.iter print_kind_solver kind_examples
