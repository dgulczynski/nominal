open Types
open Permutation

let string_of_list string_of_item = function
  | []      -> "[]"
  | [x]     -> "[" ^ string_of_item x ^ "]"
  | x :: xs ->
      List.fold_left (fun acc x -> acc ^ "; " ^ string_of_item x) ("[" ^ string_of_item x) xs ^ "]"

let string_of_atom_arg (A a) = a

let rec string_of_permutation pi =
  List.fold_left
    (fun str (a, b) -> "(" ^ string_of_atom a ^ " " ^ string_of_atom b ^ ")" ^ str)
    "" pi

and string_of_atom {perm= pi; symb= a} = string_of_permutation pi ^ string_of_atom_arg a

let string_of_var_arg (V v) = v

let string_of_var {perm= pi; symb= x} = string_of_permutation pi ^ string_of_var_arg x

let rec string_of_term = function
  | Atom a       -> string_of_atom a
  | Var v        -> string_of_var v
  | Lam (a, t)   -> string_of_atom a ^ "." ^ string_of_term t
  | App (t1, t2) -> string_of_term t1 ^ " " ^ string_of_term t2
  | Fun f        -> f

let string_of_constr = function
  | Eq (t1, t2)        -> string_of_term t1 ^ " =: " ^ string_of_term t2
  | Fresh (a, t)       -> string_of_atom_arg a ^ " #: " ^ string_of_term t
  | AtomEq (a, alpha)  -> string_of_atom_arg a ^ " ==: " ^ string_of_atom alpha
  | AtomNeq (a, alpha) -> string_of_atom_arg a ^ " =/=: " ^ string_of_atom alpha
  | Shape (t1, t2)     -> string_of_term t1 ^ " ~: " ^ string_of_term t2
  | Subshape (t1, t2)  -> string_of_term t1 ^ " <: " ^ string_of_term t2

let string_of_fvar (V x) = x

let rec string_of_formula =
  let string_of_inner_formula f = "(" ^ string_of_formula f ^ ")" in
  let string_of_binop f1 op f2 = string_of_inner_formula f1 ^ op ^ string_of_inner_formula f2 in
  function
  | F_Bot               -> "⊥"
  | F_Var x             -> string_of_fvar x
  | F_Constr c          -> string_of_constr c
  | F_And (f1, f2)      -> string_of_binop f1 " ∧ " f2
  | F_Or (f1, f2)       -> string_of_binop f1 " ∨ " f2
  | F_Impl (f1, f2)     -> string_of_binop f1 " ⇒ " f2
  | F_ForallTerm (x, f) -> "∀ " ^ string_of_var_arg x ^ ". " ^ string_of_inner_formula f
  | F_ForallAtom (a, f) -> "∀ " ^ string_of_atom_arg a ^ ". " ^ string_of_inner_formula f
  | F_ExistsTerm (x, f) -> "∃ " ^ string_of_var_arg x ^ ". " ^ string_of_inner_formula f
  | F_ExistsAtom (a, f) -> "∃ " ^ string_of_atom_arg a ^ ". " ^ string_of_inner_formula f
  | F_ConstrAnd (c, f)  -> "[" ^ string_of_constr c ^ "] ∧ " ^ string_of_inner_formula f
  | F_ConstrImpl (c, f) -> "[" ^ string_of_constr c ^ "] ⇒ " ^ string_of_inner_formula f
  | F_Fun (x, f)        -> string_of_var_arg x ^ " → " ^ string_of_inner_formula f
  | F_FunTerm (x, f)    -> string_of_var_arg x ^ " → " ^ string_of_inner_formula f
  | F_FunAtom (a, f)    -> string_of_atom_arg a ^ " → " ^ string_of_inner_formula f
  | F_App (f1, f2)      -> string_of_binop f1 "" f2
  | F_AppTerm (f, e)    -> string_of_inner_formula f ^ " " ^ string_of_term e
  | F_AppAtom (f, a)    -> string_of_inner_formula f ^ " " ^ string_of_atom a
  | F_Fix (x, y, f)     ->
      "fix " ^ string_of_var_arg x ^ "(" ^ string_of_var_arg y ^ ") : " ^ string_of_inner_formula f

let rec string_of_kind = function
  | Prop                     -> "Prop"
  | Arrow ((Prop as k1), k2) -> string_of_kind k1 ^ " -> " ^ string_of_kind k2
  | Arrow (k1, k2)           -> "(" ^ string_of_kind k1 ^ ") -> " ^ string_of_kind k2
  | ForallAtom (a, k)        -> "∀ " ^ string_of_atom_arg a ^ ". " ^ string_of_kind k
  | ForallTerm (x, k)        -> "∀ " ^ string_of_var_arg x ^ ". " ^ string_of_kind k
  | Constr (c, k)            -> "[" ^ string_of_constr c ^ "] " ^ string_of_kind k
