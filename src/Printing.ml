open Types
open Permutation

let rec string_of_permutation pi =
  List.fold_left
    (fun str (a, b) -> "(" ^ string_of_atom a ^ " " ^ string_of_atom b ^ ")" ^ str)
    "" pi

and string_of_atom = function
  | {perm= []; symb= A a} -> a
  | {perm= pi; symb= A a} -> string_of_permutation pi ^ a

let string_of_var = function
  | {perm= []; symb= V x} -> x
  | {perm= pi; symb= V x} -> string_of_permutation pi ^ x

let rec string_of_term = function
  | Atom a       -> string_of_atom a
  | Var v        -> string_of_var v
  | Lam (a, t)   -> string_of_atom a ^ "." ^ string_of_term t
  | App (t1, t2) -> string_of_term t1 ^ " " ^ string_of_term t2
  | Fun f        -> f

let string_of_constr = function
  | Fresh (A a, t)       -> a ^ " #: " ^ string_of_term t
  | Eq (t1, t2)          -> string_of_term t1 ^ " =: " ^ string_of_term t2
  | AtomEq (A a, alpha)  -> a ^ " ==: " ^ string_of_atom alpha
  | AtomNeq (A a, alpha) -> a ^ " !=: " ^ string_of_atom alpha
  | Shape (t1, t2)       -> string_of_term t1 ^ " ~: " ^ string_of_term t2
  | Subshape (t1, t2)    -> string_of_term t1 ^ " <: " ^ string_of_term t2
