open Common
open Substitution
open Types
open Permutation

let fix_kind x y k =
  (*  G, X : (forall y, [y < x] => K{y/x}) |- F : K  *)
  (* ----------------------------------------------- *)
  (*        G |- fix X(x). (F : K) : forall x, K     *)
  K_ForallTerm (y, K_Constr (var y <: var x, subst_var_in_kind x (var y) k))

let fix_binder fix_name fix_rep x y k =
  let fix_k = fix_kind x y k in
  FV_Bind (fix_name, fix_rep, fix_k)

let fix fix_name fix_rep x y k f =
  let fix = fix_binder fix_name fix_rep x y k in
  F_Fix (fix, x, k, f)

let merge_names xs ys = List.merge compare xs ys

let rec free_names_of_permutation perm =
  List.fold_left (fun acc -> merge_names acc % free_names_of_swap) [] perm

and free_names_of_permuted {perm; symb= A a} = merge_names [a] (free_names_of_permutation perm)

and free_names_of_swap (a1, a2) =
  merge_names (free_names_of_permuted a1) (free_names_of_permuted a2)

let rec free_names_of_term = function
  | T_App (t1, t2)               -> merge_names (free_names_of_term t1) (free_names_of_term t2)
  | T_Lam ({perm; symb= A a}, t) ->
      List.filter (not % ( = ) a)
      $ merge_names (free_names_of_permutation perm) (free_names_of_term t)
  | T_Var {perm; symb= V x}      -> merge_names [x] (free_names_of_permutation perm)
  | T_Atom {perm; symb= A a}     -> merge_names [a] (free_names_of_permutation perm)
  | T_Fun _                      -> []

let free_names_of_constr = function
  | C_Fresh (A a, t) -> merge_names [a] (free_names_of_term t)
  | C_AtomEq (A a1, a2) | C_AtomNeq (A a1, a2) -> merge_names [a1] (free_names_of_term (T_Atom a2))
  | C_Eq (t1, t2) | C_Shape (t1, t2) | C_Subshape (t1, t2) ->
      merge_names (free_names_of_term t1) (free_names_of_term t2)

let rec free_names_of_formula = function
  | F_Bot | F_Top | F_Var _ -> []
  | F_App (f1, f2) | F_Impl (f1, f2) ->
      merge_names (free_names_of_formula f1) (free_names_of_formula f2)
  | F_Or fs | F_And fs -> List.fold_left (fun acc -> merge_names acc % free_names_of_formula) [] fs
  | F_Constr c -> free_names_of_constr c
  | F_ConstrAnd (c, f) | F_ConstrImpl (c, f) ->
      merge_names (free_names_of_constr c) (free_names_of_formula f)
  | F_AppAtom (f, A a) -> merge_names [a] (free_names_of_formula f)
  | F_AppTerm (f, t) -> merge_names (free_names_of_term t) (free_names_of_formula f)
  | F_FunAtom (A name, f)
  | F_FunTerm (V name, f)
  | F_ForallAtom (A name, f)
  | F_ForallTerm (V name, f)
  | F_ExistsAtom (A name, f)
  | F_ExistsTerm (V name, f)
  | F_Fix (_, V name, _, f) -> List.filter (not % ( = ) name) (free_names_of_formula f)
  | F_Fun (_, f) -> free_names_of_formula f
