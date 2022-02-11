open Types
open Permutation
open Common

let rec subst_perm sub =
  List.map (fun ({perm= pi1; symb= a1}, {perm= pi2; symb= a2}) ->
      ({perm= subst_perm sub pi1; symb= sub a1}, {perm= subst_perm sub pi2; symb= sub a2}) )

let subst a b c = if c = a then b else c

let sub_perm_atom sub_atom {perm= pi; symb= a} = {perm= subst_perm sub_atom pi; symb= sub_atom a}

let rec subst_in_term sub_atom sub_var = function
  | T_Atom alpha              -> T_Atom (sub_perm_atom sub_atom alpha)
  | T_Var {perm= pi; symb= x} -> permute_term (subst_perm sub_atom pi) (sub_var x)
  | T_Lam (alpha, t)          -> T_Lam
                                   (sub_perm_atom sub_atom alpha, subst_in_term sub_atom sub_var t)
  | T_App (t1, t2)            -> T_App
                                   ( subst_in_term sub_atom sub_var t1
                                   , subst_in_term sub_atom sub_var t2 )
  | T_Fun f                   -> T_Fun f

let subst_atom_in_term a b = subst_in_term (subst a b) (fun x -> var x)

let subst_var_in_term x t = subst_in_term id (fun y -> if y = x then t else var y)

let subst_in_constr sub_atom sub_term = function
  | C_Fresh (a, t)       -> C_Fresh (sub_atom a, sub_term t)
  | C_Eq (t1, t2)        -> C_Eq (sub_term t1, sub_term t2)
  | C_Shape (t1, t2)     -> C_Shape (sub_term t1, sub_term t2)
  | C_Subshape (t1, t2)  -> C_Subshape (sub_term t1, sub_term t2)
  | C_AtomEq (a, alpha)  -> C_AtomEq (sub_atom a, sub_perm_atom sub_atom alpha)
  | C_AtomNeq (a, alpha) -> C_AtomNeq (sub_atom a, sub_perm_atom sub_atom alpha)

let subst_atom_in_constr a b = subst_in_constr (subst a b) (subst_atom_in_term a b)

let subst_var_in_constr x t = subst_in_constr id (subst_var_in_term x t)

let rec subst_atom_in_kind a b k =
  let sub = subst_atom_in_kind a b in
  match k with
  | K_Prop               -> K_Prop
  | K_Arrow (k1, k2)     -> K_Arrow (sub k1, sub k2)
  | K_ForallTerm (x, k)  -> K_ForallTerm (x, sub k)
  | K_ForallAtom (a', k) -> if a = a' then K_ForallAtom (a', k) else K_ForallAtom (a', sub k)
  | K_Constr (c, k)      -> K_Constr (subst_atom_in_constr a b c, sub k)

let rec subst_var_in_kind x y k =
  let sub = subst_var_in_kind x y in
  match k with
  | K_Prop               -> K_Prop
  | K_Arrow (k1, k2)     -> K_Arrow (sub k1, sub k2)
  | K_ForallTerm (x, k)  -> if x = y then K_ForallTerm (x, k) else K_ForallTerm (x, sub k)
  | K_ForallAtom (a', k) -> K_ForallAtom (a', sub k)
  | K_Constr (c, k)      -> K_Constr (subst_var_in_constr x (var y) c, sub k)
