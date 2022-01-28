open Types
open Permutation
open Common

let rec subst_perm sub =
  List.map (fun ({perm= pi1; symb= a1}, {perm= pi2; symb= a2}) ->
      ({perm= subst_perm sub pi1; symb= sub a1}, {perm= subst_perm sub pi2; symb= sub a2}) )

let subst a b c = if c = a then b else c

let sub_perm_atom sub_atom {perm= pi; symb= a} = {perm= subst_perm sub_atom pi; symb= sub_atom a}

let rec subst_in_term sub_atom sub_var = function
  | Atom alpha              -> Atom (sub_perm_atom sub_atom alpha)
  | Var {perm= pi; symb= x} -> permute_term (subst_perm sub_atom pi) (sub_var x)
  | Lam (alpha, t)          -> Lam (sub_perm_atom sub_atom alpha, subst_in_term sub_atom sub_var t)
  | App (t1, t2)            -> App
                                 ( subst_in_term sub_atom sub_var t1
                                 , subst_in_term sub_atom sub_var t2 )
  | Fun f                   -> Fun f

let subst_atom_in_term a b = subst_in_term (subst a b) (fun x -> Var (pure x))

let subst_var_in_term x t = subst_in_term id (fun y -> if y = x then t else Var (pure y))

let subst_in_constr sub_atom sub_term = function
  | Fresh (a, t)       -> Fresh (sub_atom a, sub_term t)
  | Eq (t1, t2)        -> Eq (sub_term t1, sub_term t2)
  | Shape (t1, t2)     -> Shape (sub_term t1, sub_term t2)
  | Subshape (t1, t2)  -> Subshape (sub_term t1, sub_term t2)
  | AtomEq (a, alpha)  -> AtomEq (sub_atom a, sub_perm_atom sub_atom alpha)
  | AtomNeq (a, alpha) -> AtomNeq (sub_atom a, sub_perm_atom sub_atom alpha)

let subst_atom_in_constr a b = subst_in_constr (subst a b) (subst_atom_in_term a b)

let subst_var_in_constr x t = subst_in_constr id (subst_var_in_term x t)

let rec subst_atom_in_kind a b k =
  let sub = subst_atom_in_kind a b in
  match k with
  | Prop               -> Prop
  | Arrow (k1, k2)     -> Arrow (sub k1, sub k2)
  | ForallTerm (x, k)  -> ForallTerm (x, sub k)
  | ForallAtom (a', k) -> if a = a' then ForallAtom (a', k) else ForallAtom (a', sub k)
  | Constr (c, k)      -> Constr (subst_atom_in_constr a b c, sub k)

let rec subst_var_in_kind x y k =
  let sub = subst_var_in_kind x y in
  match k with
  | Prop               -> Prop
  | Arrow (k1, k2)     -> Arrow (sub k1, sub k2)
  | ForallTerm (x, k)  -> if x = y then ForallTerm (x, k) else ForallTerm (x, sub k)
  | ForallAtom (a', k) -> ForallAtom (a', sub k)
  | Constr (c, k)      -> Constr (subst_var_in_constr x (Var (pure y)) c, sub k)
