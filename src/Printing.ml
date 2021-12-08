open Types

let string_of_atom = function Just (A a) -> a | Permuted (_, A a) -> "pi " ^ a

let string_of_var = function Just (V x) -> x | Permuted (_, V x) -> "pi " ^ x

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
