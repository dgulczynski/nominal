open Types
open Permutation
open Format
open Common
open Utils

type 'a printer = formatter -> 'a -> unit

let print_space fmt () = pp_print_string fmt " "

let string_of_list' ?(left = "[") ?(sep = "; ") ?(right = "]") string_of_item =
  let brace = flip (Printf.sprintf "%s%s%s" left) right in
  function
  | []      -> brace ""
  | [x]     -> brace (string_of_item x)
  | x :: xs ->
      brace
      $ List.fold_left (fun acc x -> Printf.sprintf "%s%s%s" acc sep $ string_of_item x) (string_of_item x) xs

let string_of_list string_of_item = string_of_list' string_of_item

let unwords = String.concat " "

let pp_print_parenthesized ?(left = '(') ?(right = ')') pp_x fmt x =
  pp_print_char fmt left ; pp_x fmt x ; pp_print_char fmt right

let pp_print_bracketed printer = pp_print_parenthesized ~left:'[' ~right:']' printer

let pp_print_rep fmt i = pp_print_string fmt "!" ; pp_print_int fmt i

let rec pp_print_swap env fmt =
  pp_print_bracketed
    (fun fmt (a, b) ->
      pp_print_atom_permuted env fmt a ; print_space fmt () ; pp_print_atom_permuted env fmt b )
    fmt

and pp_print_permutation env fmt =
  let pp_sep = const2 () in
  pp_print_list ~pp_sep (pp_print_swap env) fmt

and pp_print_atom_permuted env fmt {perm= pi; symb= a} =
  pp_print_permutation env fmt pi ; pp_print_atom env fmt a

and pp_print_atom env fmt (A a) =
  match bind_by_rep a env with
  | Some (Bind (a_name, K_Atom _)) -> pp_print_string fmt a_name
  | _                              -> pp_print_rep fmt a

let pp_print_var env fmt (V x) =
  match bind_by_rep x env with
  | Some (Bind (x_name, K_Var _)) -> pp_print_string fmt x_name
  | _                             -> pp_print_rep fmt x

let pp_print_var_permuted env fmt {perm= pi; symb= x} =
  pp_print_permutation env fmt pi ; pp_print_var env fmt x

let rec pp_print_term_in_env env fmt = function
  | T_Atom a       -> pp_print_atom_permuted env fmt a
  | T_Var v        -> pp_print_var_permuted env fmt v
  | T_Lam (a, t)   -> pp_print_atom_permuted env fmt a ; pp_print_char fmt '.' ; pp_print_term_in_env env fmt t
  | T_App (t1, t2) -> (
      ( match t1 with
      | T_Atom _ | T_Var _ | T_App _ | T_Fun _ -> pp_print_term_in_env env fmt t1
      | T_Lam _ -> pp_print_parenthesized (pp_print_term_in_env env) fmt t1 ) ;
      print_space fmt () ;
      match t2 with
      | T_Atom _ | T_Var _ | T_Fun _ -> pp_print_term_in_env env fmt t2
      | T_Lam _ | T_App _            -> pp_print_parenthesized (pp_print_term_in_env env) fmt t2 )
  | T_Fun f        -> pp_print_string fmt f

let pp_print_term = pp_print_term_in_env []

let rec pp_print_shape env fmt = function
  | S_Var x        -> pp_print_var env fmt x
  | S_Atom         -> pp_print_string fmt "_"
  | S_Lam s        -> pp_print_string fmt "_." ; pp_print_shape env fmt s
  | S_App (s1, s2) -> (
      ( match s1 with
      | S_Var _ | S_Atom | S_App _ | S_Fun _ -> pp_print_shape env fmt s1
      | S_Lam _                              -> pp_print_parenthesized (pp_print_shape env) fmt s1 ) ;
      print_space fmt () ;
      match s2 with
      | S_Var _ | S_Atom | S_Fun _ -> pp_print_shape env fmt s2
      | S_Lam _ | S_App _          -> pp_print_parenthesized (pp_print_shape env) fmt s2 )
  | S_Fun f        -> pp_print_string fmt f

let pp_print_quantifier fmt quantifier variable = function
  | None      -> pp_print_string fmt (sprintf "%s %s." quantifier variable)
  | Some kind -> pp_print_string fmt (sprintf "%s %s:%s." quantifier variable kind)

let pp_forall fmt variable kind = pp_print_quantifier fmt "∀" variable (Some kind)

let pp_exists fmt variable kind = pp_print_quantifier fmt "∃" variable (Some kind)

let pp_print_constr_in_env env fmt c =
  let print_binop t1 op t2 =
    pp_print_term_in_env env fmt t1 ;
    print_space fmt () ;
    pp_print_string fmt op ;
    print_space fmt () ;
    pp_print_term_in_env env fmt t2
  in
  match c with
  | C_Eq (t1, t2)        -> print_binop t1 "=" t2
  | C_Shape (t1, t2)     -> print_binop t1 "~" t2
  | C_Subshape (t1, t2)  -> print_binop t1 "<" t2
  | C_Fresh (a, t)       -> print_binop (atom a) "#" t
  | C_AtomEq (a, alpha)  -> print_binop (atom a) "==" $ T_Atom alpha
  | C_AtomNeq (a, alpha) -> print_binop (atom a) "=/=" $ T_Atom alpha

let pp_print_constr = pp_print_constr_in_env []

let rec pp_print_kind_in_env env fmt k =
  let rec print_foralls env = function
    | K_ForallAtom ((A_Bind (a_name, _) as a_bind), k) -> (
        let env' = atom_binder_to_binder a_bind :: env in
        pp_print_string fmt a_name ;
        print_space fmt () ;
        match k with
        | K_ForallAtom _ -> print_foralls env' k
        | _              -> pp_print_string fmt ": atom." ; pp_print_kind_in_env env' fmt k )
    | K_ForallTerm ((V_Bind (x_name, _) as x_bind), k) -> (
        let env' = var_binder_to_binder x_bind :: env in
        pp_print_string fmt x_name ;
        print_space fmt () ;
        match k with
        | K_ForallTerm _ -> print_foralls env' k
        | _              -> pp_print_string fmt ": term." ; pp_print_kind_in_env env' fmt k )
    | k -> pp_print_kind_in_env env fmt k
  in
  match k with
  | K_Prop                          -> pp_print_char fmt '*'
  | K_Arrow (K_Prop, k2)            -> pp_print_string fmt "* ->" ;
                                       print_space fmt () ;
                                       pp_print_kind_in_env env fmt k2
  | K_Arrow (k1, k2)                ->
      pp_print_parenthesized (pp_print_kind_in_env env) fmt k1 ;
      print_space fmt () ;
      pp_print_string fmt "->" ;
      print_space fmt () ;
      pp_print_kind_in_env env fmt k2
  | K_ForallAtom _ | K_ForallTerm _ -> pp_print_string fmt "∀ " ; print_foralls env k
  | K_Constr (c, k)                 ->
      pp_print_bracketed (pp_print_constr_in_env env) fmt c ;
      pp_print_kind_in_env env fmt k

let pp_print_kind = pp_print_kind_in_env []

let pp_print_with_prefix prefix printer fmt x = pp_print_string fmt prefix ; printer fmt x

let pp_print_fvar env fmt (FV x) =
  match bind_by_rep x env with
  | Some (Bind (x_name, K_FVar _)) -> pp_print_string fmt x_name
  | _                              -> pp_print_rep fmt x

let rec pp_print_formula env fmt formula =
  let is_atomic = function
    | F_Bot | F_Top | F_Var _ -> true
    | _                       -> false
  in
  let pp_formula = pp_print_formula env fmt in
  let pp_string = pp_print_string fmt in
  let space () = print_space fmt () in
  let pp_fun print_var var print_kind kind formula env =
    pp_string "fun" ;
    space () ;
    print_var fmt var ;
    pp_print_char fmt ':' ;
    print_kind fmt kind ;
    space () ;
    pp_string "->" ;
    space () ;
    pp_print_formula env fmt formula
  in
  let pp_sep sep fmt () = pp_print_string fmt sep in
  let pp_print_atomic_formula fmt f =
    if is_atomic f then pp_print_formula env fmt f else pp_print_parenthesized (pp_print_formula env) fmt f
  in
  let pp_print_conclusion f =
    match f with
    | F_Impl _ | F_ConstrImpl _ | F_Bot | F_Top | F_Var _ -> pp_formula f
    | _ -> pp_print_parenthesized (pp_print_formula env) fmt f
  in
  let pp_print_app_left f =
    match f with
    | F_App _ | F_AppTerm _ | F_AppAtom _ -> pp_formula f
    | _                                   -> pp_print_atomic_formula fmt f
  in
  let rec pp_print_foralls env = function
    | F_ForallTerm ((V_Bind (_, x) as x_bind), (F_ForallTerm _ as f))
    | F_ExistsTerm ((V_Bind (_, x) as x_bind), (F_ExistsTerm _ as f)) ->
        let env = var_binder_to_binder x_bind :: env in
        pp_print_var env fmt x ; space () ; pp_print_foralls env f
    | F_ForallTerm ((V_Bind (_, x) as x_bind), f) | F_ExistsTerm ((V_Bind (_, x) as x_bind), f) ->
        let env = var_binder_to_binder x_bind :: env in
        pp_print_var env fmt x ;
        print_space fmt () ;
        pp_print_string fmt ": term. " ;
        pp_print_formula env fmt f
    | F_ForallAtom ((A_Bind (_, a) as a_bind), (F_ForallAtom _ as f))
    | F_ExistsAtom ((A_Bind (_, a) as a_bind), (F_ExistsAtom _ as f)) ->
        let env = atom_binder_to_binder a_bind :: env in
        pp_print_atom env fmt a ; space () ; pp_print_foralls env f
    | F_ForallAtom ((A_Bind (_, a) as a_bind), f) | F_ExistsAtom ((A_Bind (_, a) as a_bind), f) ->
        let env = atom_binder_to_binder a_bind :: env in
        pp_print_atom env fmt a ;
        print_space fmt () ;
        pp_print_string fmt ": atom. " ;
        pp_print_formula env fmt f
    | _ -> failwith ""
  in
  let pp_print_under_binop fmt = function
    | "", f   -> pp_print_atomic_formula fmt f
    | name, f -> pp_print_string fmt name ; pp_print_string fmt ": " ; pp_print_atomic_formula fmt f
  in
  match formula with
  | F_Bot -> pp_string "⊥"
  | F_Top -> pp_string "⊤"
  | F_Var x -> pp_print_fvar env fmt x
  | F_And fs -> pp_print_list ~pp_sep:(pp_sep " ∧ ") pp_print_under_binop fmt fs
  | F_Or fs -> pp_print_list ~pp_sep:(pp_sep " ∨ ") pp_print_under_binop fmt fs
  | F_Constr c -> (pp_print_constr_in_env env) fmt c
  | F_Impl (f1, f2) ->
      pp_print_atomic_formula fmt f1 ; space () ; pp_string "=>" ; space () ; pp_print_conclusion f2
  | F_ForallAtom _ | F_ForallTerm _ -> pp_print_string fmt "∀ " ; pp_print_foralls env formula
  | F_ExistsAtom _ | F_ExistsTerm _ -> pp_print_string fmt "∃ " ; pp_print_foralls env formula
  | F_ConstrAnd (c, f) ->
      pp_print_bracketed (pp_print_constr_in_env env) fmt c ;
      space () ;
      pp_string "∧" ;
      space () ;
      pp_formula f
  | F_ConstrImpl (c, f) -> (
      pp_print_bracketed (pp_print_constr_in_env env) fmt c ;
      space () ;
      pp_string "=>" ;
      space () ;
      match f with
      | F_ConstrImpl _ -> pp_formula f
      | _              -> pp_print_conclusion f )
  | F_Fun (FV_Bind (x_name, x, k), f) ->
      let env = Bind (x_name, K_FVar (x, k)) :: env in
      pp_fun pp_print_string x_name pp_print_kind k f env
  | F_FunTerm ((V_Bind (x_name, _) as x_bind), f) ->
      pp_fun pp_print_string x_name pp_print_string "term" f (var_binder_to_binder x_bind :: env)
  | F_FunAtom ((A_Bind (a_name, _) as a_bind), f) ->
      pp_fun pp_print_string a_name pp_print_string "atom" f (atom_binder_to_binder a_bind :: env)
  | F_App (f1, f2) -> pp_print_app_left f1 ; space () ; pp_print_atomic_formula fmt f2
  | F_AppTerm (f, e) ->
      pp_print_app_left f ; space () ; pp_string "{" ; pp_print_term_in_env env fmt e ; pp_string "}"
  | F_AppAtom (f, a) -> pp_print_app_left f ; space () ; pp_print_atom_permuted env fmt a
  | F_Fix (FV_Bind (fix_name, fix, fix_k), (V_Bind (_, x) as x_bind), k, f) ->
      let env = var_binder_to_binder x_bind :: Bind (fix_name, K_FVar (fix, fix_k)) :: env in
      pp_print_string fmt "fix" ;
      space () ;
      pp_print_string fmt fix_name ;
      pp_print_parenthesized (pp_print_var env) fmt x ;
      pp_print_string fmt ": " ;
      pp_print_kind fmt k ;
      pp_print_char fmt '.' ;
      space () ;
      pp_print_formula env fmt f

let pp_print_binder fmt = function
  | Bind (name, K_Atom _)      -> pp_print_string fmt (name ^ " : atom")
  | Bind (name, K_Var _)       -> pp_print_string fmt (name ^ " : var")
  | Bind (name, K_Func)        -> pp_print_string fmt (name ^ " : func")
  | Bind (name, K_FVar (x, k)) ->
      pp_print_string fmt (name ^ " : ") ;
      pp_print_kind fmt k ;
      pp_print_parenthesized pp_print_int fmt x

let pp_print_bound_env =
  let pp_sep fmt () = pp_print_string fmt "; " in
  pp_print_bracketed $ pp_print_list ~pp_sep pp_print_binder

let printer_to_string pp_print_thing thing = Format.asprintf "%a" pp_print_thing thing

let string_of_permutation pi = printer_to_string (pp_print_permutation []) pi

let string_of_atom = printer_to_string (pp_print_atom_permuted [])

let string_of_var = printer_to_string (pp_print_var_permuted [])

let string_of_fvar = printer_to_string $ pp_print_fvar []

let string_of_fvar_in_env env = printer_to_string $ pp_print_fvar env

let string_of_shape = printer_to_string (pp_print_shape [])

let string_of_term = printer_to_string pp_print_term

let string_of_constr = printer_to_string pp_print_constr

let string_of_kind = printer_to_string pp_print_kind

let string_of_formula = printer_to_string $ pp_print_formula []

let string_of_formula_in_env env = printer_to_string $ pp_print_formula env

let string_of_bound_env = printer_to_string pp_print_bound_env
