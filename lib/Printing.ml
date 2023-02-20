open Types
open Permutation
open Format
open Common

type 'a printer = formatter -> 'a -> unit

let print_space fmt () = pp_print_string fmt " "

let string_of_list string_of_item ?(sep = "; ") = function
  | []      -> "[]"
  | [x]     -> "[" ^ string_of_item x ^ "]"
  | x :: xs ->
      List.fold_left (fun acc x -> acc ^ sep ^ string_of_item x) ("[" ^ string_of_item x) xs ^ "]"

let string_of_atom_arg (A a) = a

let string_of_var_arg (V v) = v

let pp_print_parenthesized ?(left = '(') ?(right = ')') pp_x fmt x =
  pp_print_char fmt left ; pp_x fmt x ; pp_print_char fmt right

let pp_print_bracketed printer = pp_print_parenthesized ~left:'[' ~right:']' printer

let rec pp_print_swap fmt =
  pp_print_bracketed
    (fun fmt (a, b) ->
      pp_print_atom_permuted fmt a ; print_space fmt () ; pp_print_atom_permuted fmt b )
    fmt

and pp_print_permutation fmt =
  let pp_sep = const2 () in
  pp_print_list ~pp_sep pp_print_swap fmt

and pp_print_atom_permuted fmt {perm= pi; symb= a} =
  pp_print_permutation fmt pi ; pp_print_atom fmt a

and pp_print_atom fmt (A a) = pp_print_string fmt a

let pp_print_var fmt (V x) = pp_print_string fmt x

let pp_print_var_permuted fmt {perm= pi; symb= x} = pp_print_permutation fmt pi ; pp_print_var fmt x

let rec pp_print_term fmt = function
  | T_Atom a       -> pp_print_atom_permuted fmt a
  | T_Var v        -> pp_print_var_permuted fmt v
  | T_Lam (a, t)   -> pp_print_atom_permuted fmt a ; pp_print_char fmt '.' ; pp_print_term fmt t
  | T_App (t1, t2) -> (
      ( match t1 with
      | T_Atom _ | T_Var _ | T_App _ | T_Fun _ -> pp_print_term fmt t1
      | T_Lam _ -> pp_print_parenthesized pp_print_term fmt t1 ) ;
      print_space fmt () ;
      match t2 with
      | T_Atom _ | T_Var _ | T_Fun _ -> pp_print_term fmt t2
      | T_Lam _ | T_App _            -> pp_print_parenthesized pp_print_term fmt t2 )
  | T_Fun f        -> pp_print_string fmt f

let rec pp_print_shape fmt = function
  | S_Var x        -> pp_print_var fmt x
  | S_Atom         -> pp_print_string fmt "_"
  | S_Lam s        -> pp_print_string fmt "_." ; pp_print_shape fmt s
  | S_App (s1, s2) -> (
      ( match s1 with
      | S_Var _ | S_Atom | S_App _ | S_Fun _ -> pp_print_shape fmt s1
      | S_Lam _ -> pp_print_parenthesized pp_print_shape fmt s1 ) ;
      print_space fmt () ;
      match s2 with
      | S_Var _ | S_Atom | S_Fun _ -> pp_print_shape fmt s2
      | S_Lam _ | S_App _          -> pp_print_parenthesized pp_print_shape fmt s2 )
  | S_Fun f        -> pp_print_string fmt f

let pp_print_quantifier fmt quantifier variable = function
  | None      -> pp_print_string fmt (sprintf "%s %s." quantifier variable)
  | Some kind -> pp_print_string fmt (sprintf "%s %s:%s." quantifier variable kind)

let pp_forall fmt variable kind = pp_print_quantifier fmt "∀" variable (Some kind)

let pp_exists fmt variable kind = pp_print_quantifier fmt "∃" variable (Some kind)

let pp_print_constr fmt c =
  let print_binop t1 op t2 =
    pp_print_term fmt t1 ;
    print_space fmt () ;
    pp_print_string fmt op ;
    print_space fmt () ;
    pp_print_term fmt t2
  in
  match c with
  | C_Eq (t1, t2)        -> print_binop t1 "=" t2
  | C_Shape (t1, t2)     -> print_binop t1 "~" t2
  | C_Subshape (t1, t2)  -> print_binop t1 "<" t2
  | C_Fresh (a, t)       -> print_binop (atom a) "#" t
  | C_AtomEq (a, alpha)  -> print_binop (atom a) "==" $ T_Atom alpha
  | C_AtomNeq (a, alpha) -> print_binop (atom a) "=/=" $ T_Atom alpha

let rec pp_print_kind fmt c =
  let pp_kind = pp_print_kind fmt in
  match c with
  | K_Prop               -> pp_print_char fmt '*'
  | K_Arrow (K_Prop, k2) -> pp_print_string fmt "* ->" ; print_space fmt () ; pp_kind k2
  | K_Arrow (k1, k2)     ->
      pp_print_parenthesized pp_print_kind fmt k1 ;
      print_space fmt () ;
      pp_print_string fmt "->" ;
      print_space fmt () ;
      pp_kind k2
  | K_ForallAtom (a, k)  ->
      pp_forall fmt (string_of_atom_arg a) "atom" ;
      print_space fmt () ;
      pp_kind k
  | K_ForallTerm (x, k)  ->
      pp_forall fmt (string_of_var_arg x) "term" ;
      print_space fmt () ;
      pp_kind k
  | K_Constr (c, k)      ->
      pp_print_bracketed pp_print_constr fmt c ;
      pp_kind k

let pp_print_with_prefix prefix printer fmt x = pp_print_string fmt prefix ; printer fmt x

let pp_print_fvar env fmt x =
  let test_map = function
    | x_name, K_FVar (x_rep, _) when x_rep = x -> Some x_name
    | _ -> None
  in
  match List.find_map test_map env with
  | Some x_name -> pp_print_string fmt x_name
  | None        -> pp_print_with_prefix "!" pp_print_int fmt x

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
    if is_atomic f then pp_print_formula env fmt f
    else pp_print_parenthesized (pp_print_formula env) fmt f
  in
  let pp_print_conclusion f =
    match f with
    | F_Impl _ | F_ConstrImpl _ | F_Bot | F_Top | F_Var _ -> pp_formula f
    | _ -> pp_print_parenthesized (pp_print_formula env) fmt f
  in
  let pp_print_app_left f =
    match f with
    | F_App _ | F_AppTerm _ | F_AppAtom _ -> pp_formula f
    | _ -> pp_print_atomic_formula fmt f
  in
  match formula with
  | F_Bot -> pp_string "⊥"
  | F_Top -> pp_string "⊤"
  | F_Var (FV x) -> pp_print_fvar env fmt x
  | F_And fs -> pp_print_list ~pp_sep:(pp_sep " ∧ ") pp_print_atomic_formula fmt fs
  | F_Or fs -> pp_print_list ~pp_sep:(pp_sep " ∨ ") pp_print_atomic_formula fmt fs
  | F_Constr c -> pp_print_constr fmt c
  | F_Impl (f1, f2) ->
      pp_print_atomic_formula fmt f1 ; space () ; pp_string "=>" ; space () ; pp_print_conclusion f2
  | F_ForallTerm (x, f) ->
      pp_forall fmt (string_of_var_arg x) "term" ;
      space () ;
      pp_formula f
  | F_ForallAtom (a, f) ->
      pp_forall fmt (string_of_atom_arg a) "atom" ;
      space () ;
      pp_formula f
  | F_ExistsTerm (x, f) ->
      pp_exists fmt (string_of_var_arg x) "term" ;
      space () ;
      pp_formula f
  | F_ExistsAtom (a, f) ->
      pp_exists fmt (string_of_atom_arg a) "atom" ;
      space () ;
      pp_formula f
  | F_ConstrAnd (c, f) ->
      pp_print_bracketed pp_print_constr fmt c ;
      space () ;
      pp_string "∧" ;
      space () ;
      pp_formula f
  | F_ConstrImpl (c, f) -> (
      pp_print_bracketed pp_print_constr fmt c ;
      space () ;
      pp_string "=>" ;
      space () ;
      match f with
      | F_ConstrImpl _ -> pp_formula f
      | _              -> pp_print_conclusion f )
  | F_Fun (FV_Bind (x_name, x, k), f) ->
      let env = (x_name, K_FVar (x, k)) :: env in
      pp_fun pp_print_string x_name pp_print_kind k f env
  | F_FunTerm (x, f) -> pp_fun pp_print_var x pp_print_string "term" f env
  | F_FunAtom (a, f) -> pp_fun pp_print_atom a pp_print_string "atom" f env
  | F_App (f1, f2) -> pp_print_app_left f1 ; space () ; pp_print_atomic_formula fmt f2
  | F_AppTerm (f, e) ->
      pp_print_app_left f ; space () ; pp_string "{" ; pp_print_term fmt e ; pp_string "}"
  | F_AppAtom (f, a) ->
      pp_print_app_left f ;
      space () ;
      pp_string (string_of_atom_arg a)
  | F_Fix (FV_Bind (fix_name, fix, fix_k), x, k, f) ->
      pp_print_string fmt "fix" ;
      space () ;
      pp_print_string fmt fix_name ;
      pp_print_parenthesized pp_print_var fmt x ;
      pp_print_char fmt ':' ;
      pp_print_kind fmt k ;
      pp_print_char fmt '.' ;
      space () ;
      let env = (fix_name, K_FVar (fix, fix_k)) :: env in
      pp_print_formula env fmt f

let pp_print_identifier_kind fmt = function
  | K_Atom        -> pp_print_string fmt "atom"
  | K_Var         -> pp_print_string fmt "var"
  | K_Func        -> pp_print_string fmt "func"
  | K_FVar (_, k) -> pp_print_kind fmt k

let pp_print_identifier_with_kind fmt (x, k) =
  pp_print_string fmt x ; pp_print_string fmt " : " ; pp_print_identifier_kind fmt k

let pp_print_identifier_env =
  let pp_sep fmt () = pp_print_string fmt "; " in
  pp_print_bracketed $ pp_print_list ~pp_sep pp_print_identifier_with_kind

let printer_to_string pp_print_thing thing = Format.asprintf "%a" pp_print_thing thing

let string_of_permutation pi = printer_to_string pp_print_permutation pi

let string_of_atom = printer_to_string pp_print_atom_permuted

let string_of_var = printer_to_string pp_print_var_permuted

let string_of_fvar = printer_to_string $ pp_print_fvar []

let string_of_fvar_in_env env = printer_to_string $ pp_print_fvar env

let string_of_shape = printer_to_string pp_print_shape

let string_of_term = printer_to_string pp_print_term

let string_of_constr = printer_to_string pp_print_constr

let string_of_kind = printer_to_string pp_print_kind

let string_of_formula = printer_to_string $ pp_print_formula []

let string_of_formula_in_env env = printer_to_string $ pp_print_formula env

let string_of_identifier_env = printer_to_string pp_print_identifier_env
