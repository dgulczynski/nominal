open Types
open Permutation

let string_of_atom_arg a = a

let rec string_of_permutation pi =
  List.fold_left
    (fun str (a, b) -> "(" ^ string_of_atom a ^ " " ^ string_of_atom b ^ ")" ^ str)
    "" pi

and string_of_atom {perm= pi; symb= A a} = string_of_permutation pi ^ string_of_atom_arg a

let string_of_var_arg v = v

let string_of_var {perm= pi; symb= V x} = string_of_permutation pi ^ string_of_var_arg x

let rec string_of_term = function
  | Atom a       -> string_of_atom a
  | Var v        -> string_of_var v
  | Lam (a, t)   -> string_of_atom a ^ "." ^ string_of_term t
  | App (t1, t2) -> string_of_term t1 ^ " " ^ string_of_term t2
  | Fun f        -> f

let string_of_constr = function
  | Eq (t1, t2)          -> string_of_term t1 ^ " =: " ^ string_of_term t2
  | Fresh (A a, t)       -> string_of_atom_arg a ^ " #: " ^ string_of_term t
  | AtomEq (A a, alpha)  -> string_of_atom_arg a ^ " ==: " ^ string_of_atom alpha
  | AtomNeq (A a, alpha) -> string_of_atom_arg a ^ " =/=: " ^ string_of_atom alpha
  | Shape (t1, t2)       -> string_of_term t1 ^ " ~: " ^ string_of_term t2
  | Subshape (t1, t2)    -> string_of_term t1 ^ " <: " ^ string_of_term t2
