open Common
open Substitution
open Types

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
