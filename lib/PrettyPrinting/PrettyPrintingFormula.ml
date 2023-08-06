open Types
open Prelude
open Utils
open PrettyPrintingCore
open PrettyPrintingTerm
open PrettyPrintingConstr

let pretty_atom_bind (A_Bind (_, a)) = pretty_atom a

let pretty_var_bind (V_Bind (_, x)) = pretty_var x

let pretty_typed x typ = pretty_binop_unbreaking x ":" typ

let pretty_quantify quantifier x kind = with_prefix_suffix (quantifier ^ " ") "." (pretty_typed x kind)

let pretty_quantify_binders to_binder pretty_bind kind quantifier binds =
  with_binders (List.rev_map to_binder binds)
  % pretty_label (pretty_quantify quantifier (unwords (List.rev_map pretty_bind binds)) (str kind))

let pretty_quantifier_atom = pretty_quantify_binders atom_binder_to_binder pretty_atom_bind "atom"

let pretty_quantifier_term = pretty_quantify_binders var_binder_to_binder pretty_var_bind "term"

let forall = "∀"

let exists = "∃"

let pretty_arrow x1 x2 = pretty_binop x1 "->" x2

let pretty_atom_bind (A_Bind (_, a)) = pretty_atom a

let pretty_var_bind (V_Bind (_, x)) = pretty_var x

let pretty_fvar (FV x) = pretty_identifier ~on_not_found:(str % Printf.sprintf "!p%d") x

let rec pretty_kind = function
  | K_Prop -> str "*"
  | K_Arrow (k1, k2) -> pretty_arrow (pretty_kind_left k1) (pretty_kind k2)
  | K_Constr (c, k) -> pretty_label (bracketed $ pretty_constr c) (pretty_kind_left k)
  | K_ForallAtom (a, k) -> pretty_kind_forall_atom [a] k
  | K_ForallTerm (x, k) -> pretty_kind_forall_term [x] k

and pretty_kind_left = function
  | K_Prop -> pretty_kind K_Prop
  | k -> parenthesized (pretty_kind k)

and pretty_kind_forall_atom atoms = function
  | K_ForallAtom (a, k) -> pretty_kind_forall_atom (a :: atoms) k
  | k -> pretty_quantifier_atom forall atoms (pretty_kind k)

and pretty_kind_forall_term vars = function
  | K_ForallTerm (x, k) -> pretty_kind_forall_term (x :: vars) k
  | k -> pretty_quantifier_term forall vars (pretty_kind k)

let pretty_bold_arrow x1 x2 = pretty_binop x1 "=>" x2

let pretty_and x1 x2 = pretty_binop x1 "∧" x2

let rec pretty_formula = function
  | F_Bot -> str "⊥"
  | F_Top -> str "⊤"
  | F_Var x -> pretty_fvar x
  | F_And fs -> pretty_multi_op "∧" (List.map pretty_named_formula fs)
  | F_Or fs -> pretty_multi_op "∨" (List.map pretty_named_formula fs)
  | (F_Impl _ | F_ConstrImpl _) as f -> pretty_formula_impl f
  | F_Constr c -> parenthesized (pretty_constr c)
  | F_ConstrAnd (c, f) -> pretty_and (bracketed $ pretty_constr c) (pretty_formula f)
  | F_ForallAtom _ as f -> pretty_formula_forall_atom [] f
  | F_ForallTerm _ as f -> pretty_formula_forall_term [] f
  | F_ExistsAtom _ as f -> pretty_formula_exists_atom [] f
  | F_ExistsTerm _ as f -> pretty_formula_exists_term [] f
  | (F_FunAtom _ | F_FunTerm _ | F_Fun _) as f -> pretty_formula_fun [] f
  | (F_AppAtom _ | F_AppTerm _ | F_App _) as f -> pretty_formula_app f
  | F_Fix (fix, x, k, f) -> pretty_fix fix x k f

and pretty_fix (FV_Bind (fix_name, fix, fix_k)) (V_Bind (x_name, _) as x_bind) k f =
  pretty_label
    (pretty_list ~left:"fix " ~sep:":" ~right:"." [with_prefix fix_name $ parenthesized (str x_name); pretty_kind k])
    (with_binders [var_binder_to_binder x_bind; Bind (fix_name, K_FVar (fix, fix_k))] $ pretty_formula f)

and pretty_formula_simple = function
  | (F_Bot | F_Top | F_Var _ | F_Constr _) as f -> pretty_formula f
  | f -> parenthesized $ pretty_formula f

and pretty_formula_impl f =
  let rec squash_impls acc = function
    | F_Impl (f1, f2) -> squash_impls (pretty_formula_simple f1 :: acc) f2
    | F_ConstrImpl (c, f2) -> squash_impls (bracketed (pretty_constr c) :: acc) f2
    | f -> (acc, f)
  in
  let premises, f = squash_impls [] f in
  pretty_bold_arrow (pretty_multi_op "=>" (List.rev premises)) (pretty_formula f)

and pretty_formula_app f =
  let rec squash_apps acc = function
    | F_App (f1, f2) -> squash_apps (pretty_formula f2 :: acc) f1
    | F_AppAtom (f, a) -> squash_apps (parenthesized (pretty_atom_permuted a) :: acc) f
    | F_AppTerm (f, t) -> squash_apps (braced (pretty_term t) :: acc) f
    | f -> (f, acc)
  in
  let f, apps = squash_apps [] f in
  pretty_label (pretty_formula f) (unwords apps)

and pretty_named_formula = function
  | "", f -> pretty_formula f
  | name, f -> with_prefix (name ^ ": ") (pretty_formula f)

and pretty_formula_forall_atom atoms = function
  | F_ForallAtom (a, f) -> pretty_formula_forall_atom (a :: atoms) f
  | f -> pretty_quantifier_atom forall atoms (pretty_formula f)

and pretty_formula_forall_term vars = function
  | F_ForallTerm (x, f) -> pretty_formula_forall_term (x :: vars) f
  | f -> pretty_quantifier_term forall vars (pretty_formula f)

and pretty_formula_exists_atom atoms = function
  | F_ExistsAtom (a, f) -> pretty_formula_exists_atom (a :: atoms) f
  | f -> pretty_quantifier_atom exists atoms (pretty_formula f)

and pretty_formula_exists_term vars = function
  | F_ExistsTerm (x, f) -> pretty_formula_exists_term (x :: vars) f
  | f -> pretty_quantifier_term exists vars (pretty_formula f)

and pretty_formula_fun xs = function
  | F_FunAtom (a, f) -> pretty_formula_fun (atom_binder_to_binder a :: xs) f
  | F_FunTerm (x, f) -> pretty_formula_fun (var_binder_to_binder x :: xs) f
  | F_Fun (x, f) -> pretty_formula_fun (fvar_binder_to_binder x :: xs) f
  | f -> pretty_label (with_prefix_suffix "fun " " ->" (pretty_binders xs)) (with_binders xs (pretty_formula f))

and pretty_binder_kind = function
  | K_Atom _ -> str "atom"
  | K_Var _ -> str "term"
  | K_FVar (_, k) -> pretty_kind k
  | K_Func -> str "symb"

and pretty_binder x =
  let x_name = str $ binder_name x in
  let x_kind = pretty_binder_kind $ binder_kind x in
  pretty_typed x_name x_kind

and pretty_binders =
  let ( <: ) k1 k2 =
    let ( <: ) = KindChecker.subkind KindCheckerEnv.empty in
    match (k1, k2) with
    | K_Atom _, K_Atom _ -> true
    | K_Var _, K_Var _ -> true
    | K_FVar (_, k1), K_FVar (_, k2) -> k1 <: k2
    | _ -> false
  in
  let pretty_binders' xs k = parenthesized $ pretty_typed (sequence $ List.map str xs) (pretty_binder_kind k) in
  let rec process_binders (xs, k) = function
    | Bind (x', k') :: xs' when k' <: k -> process_binders (x' :: xs, k) xs'
    | Bind (x', k') :: xs' -> sequence $ [process_binders ([x'], k') xs'; pretty_binders' xs k]
    | [] -> pretty_binders' xs k
  in
  function
  | [] -> assert false
  | [x] -> pretty_binder x
  | Bind (x, k) :: xs -> process_binders ([x], k) xs

let pretty_solve assms goal =
  pretty_label (pretty_ocaml_list $ List.map pretty_constr assms) (with_prefix "⊢ " $ pretty_formula goal)

let pretty_bound_env = pretty_ocaml_list % List.map pretty_binder
