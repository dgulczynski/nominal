open Types
open Permutation
open Common

exception SubstExn of string

module NameInternal = struct
  type t = name_internal

  let compare = compare
end

module type SubstType = Map.S with type key = name_internal

module Subst = Map.Make (NameInternal)

type subst_target = ST_Atom of permuted_atom | ST_Var of term | ST_FVar of formula

let on_wrong_target x expected actual =
  let exn =
    Printf.sprintf "Expected %d to be %s but it's %s" x expected
      ( match actual with
      | ST_Atom _ -> "atom"
      | ST_Var _  -> "term"
      | ST_FVar _ -> "fvar" )
  in
  raise $ SubstExn exn

let sub_atom env (A a) =
  match Subst.find_opt a env with
  | Some (ST_Atom a') -> a'
  | Some t            -> on_wrong_target a "atom" t
  | None              -> pure (A a)

let sub_var env (V x) =
  match Subst.find_opt x env with
  | Some (ST_Var t) -> t
  | Some t          -> on_wrong_target x "term" t
  | None            -> var (V x)

let sub_fvar env (FV x) =
  match Subst.find_opt x env with
  | Some (ST_FVar f) -> f
  | Some t           -> on_wrong_target x "fvar" t
  | None             -> F_Var (FV x)

let add_atom (A a) a' = Subst.add a (ST_Atom a')

let add_var (V x) t = Subst.add x (ST_Var t)

let add_fvar (FV x) f = Subst.add x (ST_FVar f)

let mk_atom_subst a b = add_atom a b Subst.empty

let mk_var_subst x t = add_var x t Subst.empty

let mk_fvar_subst x t = add_fvar x t Subst.empty

let rec subst_perm sub =
  List.map (fun (alpha1, alpha2) -> (sub_perm_atom sub alpha1, sub_perm_atom sub alpha2))

and sub_perm_atom sub {perm= pi; symb= a} = permute (subst_perm sub pi) (sub_atom sub a)

let rec permute_term (pi : atom permutation) = function
  | T_Atom a       -> T_Atom (permute pi a)
  | T_Var x        -> T_Var (permute pi x)
  | T_Lam (a, t)   -> T_Lam (permute pi a, permute_term pi t)
  | T_App (t1, t2) -> T_App (permute_term pi t1, permute_term pi t2)
  | T_Fun _ as t   -> t

let rec subst_in_term sub = function
  | T_Atom alpha              -> T_Atom (sub_perm_atom sub alpha)
  | T_Var {perm= pi; symb= x} -> permute_term (subst_perm sub pi) (sub_var sub x)
  | T_Lam (alpha, t)          -> T_Lam (sub_perm_atom sub alpha, subst_in_term sub t)
  | T_App (t1, t2)            -> T_App (subst_in_term sub t1, subst_in_term sub t2)
  | T_Fun f                   -> T_Fun f

let subst_in_constr sub = function
  | C_Fresh (a, t)       -> (
    match sub_atom sub a with
    | {perm= pi; symb= a} -> C_Fresh (a, permute_term (reverse pi) $ subst_in_term sub t) )
  | C_Eq (t1, t2)        -> C_Eq (subst_in_term sub t1, subst_in_term sub t2)
  | C_Shape (t1, t2)     -> C_Shape (subst_in_term sub t1, subst_in_term sub t2)
  | C_Subshape (t1, t2)  -> C_Subshape (subst_in_term sub t1, subst_in_term sub t2)
  | C_AtomEq (a, alpha)  -> (
    match sub_atom sub a with
    | {perm= pi; symb= a} -> C_AtomEq (a, permute (reverse pi) $ sub_perm_atom sub alpha) )
  | C_AtomNeq (a, alpha) -> (
    match sub_atom sub a with
    | {perm= pi; symb= a} -> C_AtomNeq (a, permute (reverse pi) $ sub_perm_atom sub alpha) )
  | C_Symbol t           -> C_Symbol (subst_in_term sub t)

let rec subst_in_kind sub k =
  match k with
  | K_Prop -> K_Prop
  | K_Arrow (k1, k2) -> K_Arrow (subst_in_kind sub k1, subst_in_kind sub k2)
  | K_ForallTerm (V_Bind (x_name, x), k') ->
      let x' = fresh_var () in
      K_ForallTerm (V_Bind (x_name, x'), subst_in_kind (add_var x (var x') sub) k')
  | K_ForallAtom (A_Bind (a_name, a), k') ->
      let a' = fresh_atom () in
      K_ForallAtom (A_Bind (a_name, a'), subst_in_kind (add_atom a (pure a') sub) k')
  | K_Constr (c, k') -> K_Constr (subst_in_constr sub c, subst_in_kind sub k')

let rec subst_var_in_shape x s = function
  | S_Var x' when x = x' -> s
  | S_Lam s' -> S_Lam (subst_var_in_shape x s s')
  | S_App (s1, s2) -> S_App (subst_var_in_shape x s s1, subst_var_in_shape x s s2)
  | (S_Var _ | S_Atom | S_Fun _) as s -> s

let rec subst_in_formula sub f =
  let subst_f = subst_in_formula sub in
  let subst_c = subst_in_constr sub in
  match f with
  | F_Bot -> F_Bot
  | F_Top -> F_Top
  | F_Var x -> sub_fvar sub x
  | F_Constr c -> F_Constr (subst_c c)
  | F_And fs -> F_And (List.map (on_snd subst_f) fs)
  | F_Or fs -> F_Or (List.map (on_snd subst_f) fs)
  | F_Impl (f1, f2) -> F_Impl (subst_f f1, subst_f f2)
  | F_ForallAtom _ ->
      let a_binder, f_a = instantiate_atom' sub f in
      F_ForallAtom (a_binder, f_a)
  | F_ExistsAtom _ ->
      let a_binder, f_a = instantiate_atom' sub f in
      F_ExistsAtom (a_binder, f_a)
  | F_FunAtom _ ->
      let a_binder, f_a = instantiate_atom' sub f in
      F_FunAtom (a_binder, f_a)
  | F_ForallTerm _ ->
      let x_binder, f_x = instantiate_var' sub f in
      F_ForallTerm (x_binder, f_x)
  | F_ExistsTerm _ ->
      let x_binder, f_x = instantiate_var' sub f in
      F_ExistsTerm (x_binder, f_x)
  | F_FunTerm _ ->
      let x_binder, f_x = instantiate_var' sub f in
      F_FunTerm (x_binder, f_x)
  | F_ConstrAnd (c, f) -> F_ConstrAnd (subst_c c, subst_f f)
  | F_ConstrImpl (c, f) -> F_ConstrImpl (subst_c c, subst_f f)
  | F_Fun (FV_Bind (x_name, x, k), f) -> F_Fun (FV_Bind (x_name, x, k), subst_f f)
  | F_App (f1, f2) -> F_App (subst_f f1, subst_f f2)
  | F_AppTerm (f, t) -> F_AppTerm (subst_f f, subst_in_term sub t)
  | F_AppAtom (f, a) -> F_AppAtom (subst_f f, sub_perm_atom sub a)
  | F_Fix (FV_Bind (fix_name, fix, fix_k), V_Bind (x_name, x), k, f) ->
      let fix' = fresh () and x' = fresh_var () in
      let sub' = sub |> add_var x (var x') |> add_fvar (FV fix) (fvar fix') in
      F_Fix (FV_Bind (fix_name, fix', fix_k), V_Bind (x_name, x'), k, subst_in_formula sub' f)

and instantiate_atom' sub = function
  | F_ForallAtom (A_Bind (a_name, a), f)
  | F_ExistsAtom (A_Bind (a_name, a), f)
  | F_FunAtom (A_Bind (a_name, a), f) ->
      let a' = fresh_atom () in
      let sub' = add_atom a (pure a') sub in
      (A_Bind (a_name, a'), subst_in_formula sub' f)
  | _ -> raise $ SubstExn "Cannot instantiate atom"

and instantiate_var' sub = function
  | F_ForallTerm (V_Bind (x_name, x), f)
  | F_ExistsTerm (V_Bind (x_name, x), f)
  | F_FunTerm (V_Bind (x_name, x), f) ->
      let x' = fresh_var () in
      let sub' = add_var x (var x') sub in
      (V_Bind (x_name, x'), subst_in_formula sub' f)
  | _ -> raise $ SubstExn "Cannot instantiate var"

let subst_atom_in_term = subst_in_term %% mk_atom_subst

let subst_var_in_term = subst_in_term %% mk_var_subst

let subst_atom_in_constr = subst_in_constr %% mk_atom_subst

let subst_var_in_constr = subst_in_constr %% mk_var_subst

let subst_atom_in_kind = subst_in_kind %% mk_atom_subst

let subst_var_in_kind = subst_in_kind %% mk_var_subst

let subst_atom_in_formula = subst_in_formula %% mk_atom_subst

let subst_var_in_formula = subst_in_formula %% mk_var_subst

let subst_fvar_in_formula = subst_in_formula %% mk_fvar_subst

let ( |-> ) = subst_atom_in_formula

let ( |=> ) = subst_var_in_formula

let ( |==> ) = subst_fvar_in_formula

let instantiate_atom = instantiate_atom' Subst.empty

let instantiate_var = instantiate_var' Subst.empty
