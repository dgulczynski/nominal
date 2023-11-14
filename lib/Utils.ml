open Prelude
open Substitution
open Types
open Permutation

let fix_kind x y y_name k =
  (*  G, X : (forall y, [y < x] => K{y/x}) |- F : K  *)
  (* ----------------------------------------------- *)
  (*        G |- fix X(x). (F : K) : forall x, K     *)
  K_ForallTerm (V_Bind (y_name, y), K_Constr (var y <: var x, subst_var_in_kind x (var y) k))

let fix_binder fix_name fix_rep x y y_name k =
  let fix_k = fix_kind x y y_name k in
  FV_Bind (fix_name, fix_rep, fix_k)

let fix fix_name fix_rep x x_name y y_name k f =
  let fix = fix_binder fix_name fix_rep x y y_name k in
  F_Fix (fix, V_Bind (x_name, x), k, f)

let merge_names xs ys = List.merge compare xs ys

let rec free_names_of_permutation perm = List.fold_left (fun acc -> merge_names acc % free_names_of_swap) [] perm

and free_names_of_permuted_atom {perm; symb= A a} = merge_names [a] (free_names_of_permutation perm)

and free_names_of_swap (a1, a2) = merge_names (free_names_of_permuted_atom a1) (free_names_of_permuted_atom a2)

let rec free_names_of_term = function
  | T_App (t1, t2) -> merge_names (free_names_of_term t1) (free_names_of_term t2)
  | T_Lam ({perm; symb= A a}, t) ->
    List.filter (( <> ) a) $ merge_names (free_names_of_permutation perm) (free_names_of_term t)
  | T_Var {perm; symb= V x} -> merge_names [x] (free_names_of_permutation perm)
  | T_Atom {perm; symb= A a} -> merge_names [a] (free_names_of_permutation perm)
  | T_Fun _ -> []

let free_names_of_constr = function
  | C_Fresh (A a, t) -> merge_names [a] (free_names_of_term t)
  | C_AtomEq (A a1, a2) | C_AtomNeq (A a1, a2) -> merge_names [a1] (free_names_of_term (T_Atom a2))
  | C_Eq (t1, t2) | C_Shape (t1, t2) | C_Subshape (t1, t2) ->
    merge_names (free_names_of_term t1) (free_names_of_term t2)
  | C_Symbol t -> free_names_of_term t

let rec free_names_of_formula = function
  | F_Bot | F_Top -> []
  | F_Var (FV name) -> [name]
  | F_App (f1, f2) | F_Impl (f1, f2) -> merge_names (free_names_of_formula f1) (free_names_of_formula f2)
  | F_Or fs | F_And fs -> List.fold_left (fun acc -> merge_names acc % free_names_of_formula % snd) [] fs
  | F_Constr c -> free_names_of_constr c
  | F_ConstrAnd (c, f) | F_ConstrImpl (c, f) -> merge_names (free_names_of_constr c) (free_names_of_formula f)
  | F_AppAtom (f, a) -> merge_names (free_names_of_permuted_atom a) (free_names_of_formula f)
  | F_AppTerm (f, t) -> merge_names (free_names_of_term t) (free_names_of_formula f)
  | F_FunAtom (A_Bind (_, A name), f)
  | F_FunTerm (V_Bind (_, V name), f)
  | F_ForallForm (FV_Bind (_, name, _), f)
  | F_ForallAtom (A_Bind (_, A name), f)
  | F_ForallTerm (V_Bind (_, V name), f)
  | F_ExistsForm (FV_Bind (_, name, _), f)
  | F_ExistsAtom (A_Bind (_, A name), f)
  | F_ExistsTerm (V_Bind (_, V name), f) -> List.filter (( <> ) name) (free_names_of_formula f)
  | F_Fix (FV_Bind (_, fix_name, _), V_Bind (_, V x_name), _, f) ->
    List.filter (not % flip List.mem [fix_name; x_name]) (free_names_of_formula f)
  | F_Fun (_, f) -> free_names_of_formula f

let bind_by_name name = List.find_opt (function Bind (name', _) -> name = name')

let bind_by_rep i =
  List.find_opt (function
    | Bind (_, K_Var i') | Bind (_, K_FVar (i', _)) | Bind (_, K_Atom i') -> i = i'
    | _ -> false )

let atom_binder_to_binder = function
  | A_Bind (a_name, A a) -> Bind (a_name, K_Atom a)

let var_binder_to_binder = function
  | V_Bind (x_name, V x) -> Bind (x_name, K_Var x)

let fvar_binder_to_binder = function
  | FV_Bind (x_name, x, x_kind) -> Bind (x_name, K_FVar (x, x_kind))
