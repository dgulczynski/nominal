open Types
open Permutation
open Common

let rec subst_perm sub =
  List.map (fun (alpha1, alpha2) -> (sub_perm_atom sub alpha1, sub_perm_atom sub alpha2))

and sub_perm_atom sub {perm= pi; symb= a} = permute (subst_perm sub pi) (sub a)

let sub a b c = if c = a then b else c

let subst a b c = sub (pure a) b (pure c)

let rec permute_term (pi : atom permutation) = function
  | T_Atom a       -> T_Atom (permute pi a)
  | T_Var x        -> T_Var (permute pi x)
  | T_Lam (a, t)   -> T_Lam (permute pi a, permute_term pi t)
  | T_App (t1, t2) -> T_App (permute_term pi t1, permute_term pi t2)
  | T_Fun _ as t   -> t

let rec subst_in_term sub_atom sub_var = function
  | T_Atom alpha              -> T_Atom (sub_perm_atom sub_atom alpha)
  | T_Var {perm= pi; symb= x} -> permute_term (subst_perm sub_atom pi) (sub_var x)
  | T_Lam (alpha, t)          -> T_Lam (sub_perm_atom sub_atom alpha, subst_in_term sub_atom sub_var t)
  | T_App (t1, t2)            -> T_App (subst_in_term sub_atom sub_var t1, subst_in_term sub_atom sub_var t2)
  | T_Fun f                   -> T_Fun f

let subst_atom_in_term a b = subst_in_term (subst a b) (fun x -> var x)

let subst_var_in_term x t = subst_in_term pure (fun y -> if y = x then t else var y)

let subst_in_constr (sub_atom : atom -> permuted_atom) sub_term = function
  | C_Fresh (a, t)       -> (
    match sub_atom a with
    | {perm= pi; symb= a} -> C_Fresh (a, permute_term pi (sub_term t)) )
  | C_Eq (t1, t2)        -> C_Eq (sub_term t1, sub_term t2)
  | C_Shape (t1, t2)     -> C_Shape (sub_term t1, sub_term t2)
  | C_Subshape (t1, t2)  -> C_Subshape (sub_term t1, sub_term t2)
  | C_AtomEq (a, alpha)  -> (
    match sub_atom a with
    | {perm= pi; symb= a} -> C_AtomEq (a, permute pi $ sub_perm_atom sub_atom alpha) )
  | C_AtomNeq (a, alpha) -> (
    match sub_atom a with
    | {perm= pi; symb= a} -> C_AtomNeq (a, permute pi $ sub_perm_atom sub_atom alpha) )

let subst_atom_in_constr a b = subst_in_constr (subst a b) (subst_atom_in_term a b)

let subst_var_in_constr x t = subst_in_constr pure (subst_var_in_term x t)

let rec subst_atom_in_kind a b k =
  let sub = subst_atom_in_kind a b in
  match k with
  | K_Prop               -> K_Prop
  | K_Arrow (k1, k2)     -> K_Arrow (sub k1, sub k2)
  | K_ForallTerm (x, k)  -> K_ForallTerm (x, sub k)
  | K_ForallAtom (a', k) -> K_ForallAtom (a', sub k) (* TODO: refresh a' *)
  | K_Constr (c, k)      -> K_Constr (subst_atom_in_constr a b c, sub k)

let rec subst_var_in_kind x t k =
  let sub = subst_var_in_kind x t in
  match k with
  | K_Prop               -> K_Prop
  | K_Arrow (k1, k2)     -> K_Arrow (sub k1, sub k2)
  | K_ForallTerm (x', k) -> K_ForallTerm (x', sub k) (* TODO: refresh x' *)
  | K_ForallAtom (a, k)  -> K_ForallAtom (a, sub k)
  | K_Constr (c, k)      -> K_Constr (subst_var_in_constr x t c, sub k)

let rec subst_atom_in_formula a1 a2 f =
  let sub = subst_atom_in_formula a1 a2 in
  let sub_constr = subst_atom_in_constr a1 a2 in
  let sub_term = subst_atom_in_term a1 a2 in
  let sub_kind = subst_atom_in_kind a1 a2 in
  match f with
  | F_Bot | F_Top | F_Var _      -> f
  | F_Constr c                   -> F_Constr (sub_constr c)
  | F_And fs                     -> F_And (List.map (on_snd sub) fs)
  | F_Or fs                      -> F_Or (List.map (on_snd sub) fs)
  | F_Impl (f1, f2)              -> F_Impl (sub f1, sub f2)
  | F_ForallTerm (x, f)          -> F_ForallTerm (x, sub f)
  | F_ForallAtom (a, f)          -> (* TODO: refresh a *) F_ForallAtom (a, sub f)
  | F_ExistsTerm (x, f)          -> F_ExistsTerm (x, sub f)
  | F_ExistsAtom (a, f)          -> (* TODO: refresh a *) F_ExistsAtom (a, sub f)
  | F_ConstrAnd (c, f)           -> F_ConstrAnd (sub_constr c, sub f)
  | F_ConstrImpl (c, f)          -> F_ConstrImpl (sub_constr c, sub f)
  | F_Fun (FV_Bind (x, i, k), f) -> F_Fun (FV_Bind (x, i, sub_kind k), sub f)
  | F_App (f1, f2)               -> F_App (sub f1, sub f2)
  | F_FunTerm (x, f)             -> F_FunTerm (x, sub f)
  | F_AppTerm (f, t)             -> F_AppTerm (sub f, sub_term t)
  | F_FunAtom (a, f)             -> (* TODO: refresh a *) F_FunAtom (a, sub f)
  | F_AppAtom (f, a)             -> F_AppAtom (sub f, sub_perm_atom (subst a1 a2) a)
  | F_Fix (fix, x, k, f)         -> F_Fix (fix, x, sub_kind k, sub f)

let rec subst_var_in_formula y t f =
  let sub = subst_var_in_formula y t in
  let sub_constr = subst_var_in_constr y t in
  let sub_term = subst_var_in_term y t in
  let sub_kind = subst_var_in_kind y t in
  match f with
  | F_Bot | F_Top | F_Var _      -> f
  | F_Constr c                   -> F_Constr (sub_constr c)
  | F_And fs                     -> F_And (List.map (on_snd sub) fs)
  | F_Or fs                      -> F_Or (List.map (on_snd sub) fs)
  | F_Impl (f1, f2)              -> F_Impl (sub f1, sub f2)
  | F_ForallTerm (x, f)          -> (* TODO: refresh x *) F_ForallTerm (x, sub f)
  | F_ForallAtom (a, f)          -> F_ForallAtom (a, sub f)
  | F_ExistsTerm (x, f)          -> (* TODO: refresh x *) F_ExistsTerm (x, sub f)
  | F_ExistsAtom (a, f)          -> F_ExistsAtom (a, sub f)
  | F_ConstrAnd (c, f)           -> F_ConstrAnd (sub_constr c, sub f)
  | F_ConstrImpl (c, f)          -> F_ConstrImpl (sub_constr c, sub f)
  | F_Fun (FV_Bind (x, i, k), f) -> F_Fun (FV_Bind (x, i, sub_kind k), sub f)
  | F_App (f1, f2)               -> F_App (sub f1, sub f2)
  | F_FunTerm (x, f)             -> (* TODO: refresh x *) F_FunTerm (x, sub f)
  | F_AppTerm (f, t)             -> F_AppTerm (sub f, sub_term t)
  | F_FunAtom (a, f)             -> F_FunAtom (a, sub f)
  | F_AppAtom (f, a)             -> F_AppAtom (sub f, a)
  | F_Fix (fix, x, k, f)         -> (* TODO: refresh x *) F_Fix (fix, x, sub_kind k, sub f)

let rec subst_var_in_shape x s = function
  | S_Var x' when x = x' -> s
  | S_Lam s' -> S_Lam (subst_var_in_shape x s s')
  | S_App (s1, s2) -> S_App (subst_var_in_shape x s s1, subst_var_in_shape x s s2)
  | (S_Var _ | S_Atom | S_Fun _) as s -> s

let rec subst_fvar_in_formula (FV y) g f =
  let sub = subst_fvar_in_formula (FV y) g in
  match f with
  | F_Var (FV x) when x = y -> g
  | F_Bot | F_Top | F_Var _ | F_Constr _ -> f
  | F_And fs -> F_And (List.map (on_snd sub) fs)
  | F_Or fs -> F_Or (List.map (on_snd sub) fs)
  | F_Impl (f1, f2) -> F_Impl (sub f1, sub f2)
  | F_ForallTerm (x, f) -> F_ForallTerm (x, sub f)
  | F_ForallAtom (a, f) -> F_ForallAtom (a, sub f)
  | F_ExistsTerm (x, f) -> F_ExistsTerm (x, sub f)
  | F_ExistsAtom (a, f) -> F_ExistsAtom (a, sub f)
  | F_ConstrAnd (c, f) -> F_ConstrAnd (c, sub f)
  | F_ConstrImpl (c, f) -> F_ConstrImpl (c, sub f)
  | F_Fun (FV_Bind (x_name, x, k), f) -> F_Fun (FV_Bind (x_name, x, k), sub f)
  | F_App (f1, f2) -> F_App (sub f1, sub f2)
  | F_FunTerm (x, f) -> F_FunTerm (x, sub f)
  | F_AppTerm (f, t) -> F_AppTerm (sub f, t)
  | F_FunAtom (a, f) -> F_FunAtom (a, sub f)
  | F_AppAtom (f, a) -> F_AppAtom (sub f, a)
  | F_Fix (FV_Bind (fix_name, fix, fix_k), x, k, f) ->
      F_Fix (FV_Bind (fix_name, fix, fix_k), x, k, if fix = y then f else sub f)

let ( |-> ) a = subst_atom_in_formula a

let ( |=> ) x = subst_var_in_formula x

let ( |==> ) y = subst_fvar_in_formula y
