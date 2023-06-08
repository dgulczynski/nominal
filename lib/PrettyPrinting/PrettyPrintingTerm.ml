open Prelude
open Types
open Permutation
open PrettyPrintingCore

let pretty_atom (A a) = pretty_identifier ~on_not_found:(str % Printf.sprintf "!a%d") a

let pretty_var (V x) = pretty_identifier ~on_not_found:(str % Printf.sprintf "!v%d") x

let rec pretty_atom_permuted {perm= pi; symb= a} = pretty_permuted pi (pretty_atom a)

and pretty_permuted pi x = concat (List.map pretty_swap pi @ [x])

and pretty_swap (a1, a2) = pretty_list ~left:"[" ~sep:"" ~right:"]" [pretty_atom_permuted a1; pretty_atom_permuted a2]

let pretty_var_permuted {perm= pi; symb= x} = pretty_permuted pi (pretty_var x)

let rec pretty_term = function
  | T_Fun f -> str f
  | T_Atom a -> pretty_atom_permuted a
  | T_Var x -> pretty_var_permuted x
  | T_Lam (a, e) -> concat [pretty_atom_permuted a; str "."; pretty_term e]
  | T_App _ as t -> pretty_term_app t

and pretty_term_app = function
  | T_App (e1, e2) -> pretty_label (pretty_term_app e1) (pretty_term_simple e2)
  | f -> pretty_term_simple f

and pretty_term_simple = function
  | (T_Atom _ | T_Var _ | T_Fun _) as t -> pretty_term t
  | t -> parenthesized (pretty_term t)
