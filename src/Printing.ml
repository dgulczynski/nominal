open Types
open Permutation

let string_of_list string_of_item ?(sep = "; ") = function
  | []      -> "[]"
  | [x]     -> "[" ^ string_of_item x ^ "]"
  | x :: xs ->
      List.fold_left (fun acc x -> acc ^ sep ^ string_of_item x) ("[" ^ string_of_item x) xs ^ "]"

let string_of_atom_arg (A a) = a

let rec string_of_permutation pi =
  List.fold_left
    (fun str (a, b) -> "(" ^ string_of_atom a ^ " " ^ string_of_atom b ^ ")" ^ str)
    "" pi

and string_of_atom {perm= pi; symb= a} = string_of_permutation pi ^ string_of_atom_arg a

let string_of_var_arg (V v) = v

let string_of_var {perm= pi; symb= x} = string_of_permutation pi ^ string_of_var_arg x

let rec string_of_term = function
  | T_Atom a       -> string_of_atom a
  | T_Var v        -> string_of_var v
  | T_Lam (a, t)   -> string_of_atom a ^ "." ^ string_of_term t
  | T_App (t1, t2) -> string_of_term t1 ^ " " ^ string_of_term t2
  | T_Fun f        -> f

let rec string_of_shape = function
  | S_Var x        -> string_of_var_arg x
  | S_Atom         -> "_"
  | S_Lam s        -> "_." ^ string_of_shape s
  | S_App (s1, s2) -> string_of_shape s1 ^ " " ^ string_of_shape s2
  | S_Fun f        -> f

let string_of_constr = function
  | C_Fresh (a, t)       -> string_of_atom_arg a ^ " #: " ^ string_of_term t
  | C_Eq (t1, t2)        -> string_of_term t1 ^ " =: " ^ string_of_term t2
  | C_AtomEq (a, alpha)  -> string_of_atom_arg a ^ " ==: " ^ string_of_atom alpha
  | C_AtomNeq (a, alpha) -> string_of_atom_arg a ^ " =/=: " ^ string_of_atom alpha
  | C_Shape (t1, t2)     -> string_of_term t1 ^ " =~: " ^ string_of_term t2
  | C_Subshape (t1, t2)  -> string_of_term t1 ^ " <: " ^ string_of_term t2

let rec string_of_kind = function
  | K_Prop                       -> "*"
  | K_Arrow ((K_Prop as k1), k2) -> string_of_kind k1 ^ " -> " ^ string_of_kind k2
  | K_Arrow (k1, k2)             -> "(" ^ string_of_kind k1 ^ ") -> " ^ string_of_kind k2
  | K_ForallAtom (a, k)          -> "∀ " ^ string_of_atom_arg a ^ ". " ^ string_of_kind k
  | K_ForallTerm (x, k)          -> "∀ " ^ string_of_var_arg x ^ ". " ^ string_of_kind k
  | K_Constr (c, k)              -> "[" ^ string_of_constr c ^ "] " ^ string_of_kind k

let string_of_fvar (FV x) = x

let rec string_of_formula =
  let string_of_inner_formula f = "(" ^ string_of_formula f ^ ")" in
  let string_of_binop f1 op f2 = string_of_inner_formula f1 ^ op ^ string_of_inner_formula f2 in
  function
  | F_Bot                -> "⊥"
  | F_Var x              -> string_of_fvar x
  | F_Constr c           -> string_of_constr c
  | F_And fs             -> string_of_list string_of_inner_formula ~sep:" ∧ " fs
  | F_Or fs              -> string_of_list string_of_inner_formula ~sep:" ∨ " fs
  | F_Impl (f1, f2)      -> string_of_binop f1 " ⇒ " f2
  | F_ForallTerm (x, f)  -> "∀ " ^ string_of_var_arg x ^ ". " ^ string_of_inner_formula f
  | F_ForallAtom (a, f)  -> "∀ " ^ string_of_atom_arg a ^ ". " ^ string_of_inner_formula f
  | F_ExistsTerm (x, f)  -> "∃ " ^ string_of_var_arg x ^ ". " ^ string_of_inner_formula f
  | F_ExistsAtom (a, f)  -> "∃ " ^ string_of_atom_arg a ^ ". " ^ string_of_inner_formula f
  | F_ConstrAnd (c, f)   -> "[" ^ string_of_constr c ^ "] ∧ " ^ string_of_inner_formula f
  | F_ConstrImpl (c, f)  -> "[" ^ string_of_constr c ^ "] ⇒ " ^ string_of_inner_formula f
  | F_Fun (x, k, f)      -> string_of_fvar x ^ ":" ^ string_of_kind k ^ " → "
                            ^ string_of_inner_formula f
  | F_FunTerm (x, f)     -> string_of_var_arg x ^ " → " ^ string_of_inner_formula f
  | F_FunAtom (a, f)     -> string_of_atom_arg a ^ " → " ^ string_of_inner_formula f
  | F_App (f1, f2)       -> string_of_binop f1 "" f2
  | F_AppTerm (f, e)     -> string_of_inner_formula f ^ " " ^ string_of_term e
  | F_AppAtom (f, a)     -> string_of_inner_formula f ^ " " ^ string_of_atom_arg a
  | F_Fix (fix, x, k, f) ->
      "fix " ^ string_of_fvar fix ^ "(" ^ string_of_var_arg x ^ ")" ^ string_of_kind k ^ " : "
      ^ string_of_inner_formula f
