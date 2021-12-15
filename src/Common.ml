open Types
open Permutation

let ( $ ) f x = f x

let ( >> ) f g x = f (g x)

let rec permute_term (pi : atom permutation) = function
  | Atom a       -> Atom (permute pi a)
  | Var x        -> Var (permute pi x)
  | Lam (a, t)   -> Lam (permute pi a, permute_term pi t)
  | App (t1, t2) -> App (permute_term pi t1, permute_term pi t2)
  | Fun _ as t   -> t

let rec subst_perm sub =
  List.map (fun ({perm= pi1; symb= a1}, {perm= pi2; symb= a2}) ->
      ({perm= subst_perm sub pi1; symb= sub a1}, {perm= subst_perm sub pi2; symb= sub a2}) )

let sub a b c = if c = a then b else c

let sub_perm_atom sub_atom {perm= pi; symb= a} =
  {perm= subst_perm sub_atom pi; symb= sub_atom a}

let rec subst sub_atom sub_var = function
  | Atom alpha              -> Atom (sub_perm_atom sub_atom alpha)
  | Var {perm= pi; symb= x} -> permute_term (subst_perm sub_atom pi) (sub_var x)
  | Lam (alpha, t)          -> Lam (sub_perm_atom sub_atom alpha, subst sub_atom sub_var t)
  | App (t1, t2)            -> App (subst sub_atom sub_var t1, subst sub_atom sub_var t2)
  | Fun f                   -> Fun f

let subst_atom a b = subst (sub a b) (fun x -> Var (pure x))

let subst_var x t = subst (fun a -> a) (fun y -> if y = x then t else Var (pure y))

let const x _ = x

let rec find_first test = function
  | [] -> (None, [])
  | x :: xs when test x -> (Some x, xs)
  | x :: xs ->
      let found, rest = find_first test xs in
      (found, x :: rest)

let subst_constr sub_atom sub_term = function
  | Fresh (a, t)       -> Fresh (sub_atom a, sub_term t)
  | Eq (t1, t2)        -> Eq (sub_term t1, sub_term t2)
  | Shape (t1, t2)     -> Shape (sub_term t1, sub_term t2)
  | Subshape (t1, t2)  -> Subshape (sub_term t1, sub_term t2)
  | AtomEq (a, alpha)  -> AtomEq (sub_atom a, sub_perm_atom sub_atom alpha)
  | AtomNeq (a, alpha) -> AtomNeq (sub_atom a, sub_perm_atom sub_atom alpha)

let subst_atom_constr a b = subst_constr (sub a b) (subst_atom a b)
