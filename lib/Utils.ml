open Common
open Substitution
open Types
open Permutation

let rec syntactic_occurs_check x = function
  | T_Var {perm= _; symb= x'} -> x' = x
  | T_Lam (_, t)              -> syntactic_occurs_check x t
  | T_App (t1, t2)            -> syntactic_occurs_check x t1 || syntactic_occurs_check x t2
  | T_Atom _ | T_Fun _        -> false

let rec free_vars_of_term = function
  | T_Var {perm= _; symb= x} -> [x]
  | T_Lam (_, t)             -> free_vars_of_term t
  | T_App (t1, t2)           -> free_vars_of_term t1 @ free_vars_of_term t2
  | T_Fun _ | T_Atom _       -> []

let fresh_generator ?(start = 0) from_number =
  let counter = ref (start - 1) in
  fun () -> incr counter ; from_number !counter

(* let string_from_number ?(prefix = "") number = prefix ^ string_of_int number *)

let fresh, fresh_atom, fresh_var, fresh_fvar =
  let generator = fresh_generator id in
  let to_atom a = A a in
  let to_var x = V x in
  let to_fvar x = FV x in
  (generator, to_atom % generator, to_var % generator, to_fvar % generator)

let rec shape_of_term = function
  | T_Var {symb= x; _} -> S_Var x
  | T_Atom _           -> S_Atom
  | T_Lam (_, t)       -> S_Lam (shape_of_term t)
  | T_App (t1, t2)     -> S_App (shape_of_term t1, shape_of_term t2)
  | T_Fun f            -> S_Fun f

let rec term_of_shape = function
  | S_Var x        ->
      let y = fresh_var () in
      (var y, [(x, y)])
  | S_Atom         -> (atom $ fresh_atom (), [])
  | S_Lam s        ->
      let t, vs = term_of_shape s in
      (T_Lam (pure $ fresh_atom (), t), vs)
  | S_App (s1, s2) ->
      let t1, vs1 = term_of_shape s1 and t2, vs2 = term_of_shape s2 in
      (T_App (t1, t2), vs1 @ vs2)
  | S_Fun f        -> (T_Fun f, [])

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

let rec free_names_of_permutation perm =
  List.fold_left (fun acc -> merge_names acc % free_names_of_swap) [] perm

and free_names_of_permuted_atom {perm; symb= A a} = merge_names [a] (free_names_of_permutation perm)

and free_names_of_swap (a1, a2) =
  merge_names (free_names_of_permuted_atom a1) (free_names_of_permuted_atom a2)

let rec free_names_of_term = function
  | T_App (t1, t2)               -> merge_names (free_names_of_term t1) (free_names_of_term t2)
  | T_Lam ({perm; symb= A a}, t) ->
      List.filter (( <> ) a) $ merge_names (free_names_of_permutation perm) (free_names_of_term t)
  | T_Var {perm; symb= V x}      -> merge_names [x] (free_names_of_permutation perm)
  | T_Atom {perm; symb= A a}     -> merge_names [a] (free_names_of_permutation perm)
  | T_Fun _                      -> []

let free_names_of_constr = function
  | C_Fresh (A a, t) -> merge_names [a] (free_names_of_term t)
  | C_AtomEq (A a1, a2) | C_AtomNeq (A a1, a2) -> merge_names [a1] (free_names_of_term (T_Atom a2))
  | C_Eq (t1, t2) | C_Shape (t1, t2) | C_Subshape (t1, t2) ->
      merge_names (free_names_of_term t1) (free_names_of_term t2)

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
  | F_ForallAtom (A_Bind (_, A name), f)
  | F_ForallTerm (V_Bind (_, V name), f)
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
