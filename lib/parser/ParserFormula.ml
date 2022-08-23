open Common
open Angstrom
open ParserTypes
open ParserCommon
open ParserTerm
open ParserKind
open ParserConstr

let f_bot = string_ci "false" <|> string "⊥" >>| const PF_Bot

let f_top = string_ci "true" <|> string "⊤" >>| const PF_Top

let f_var = identifier >>| fun x -> PF_Var x

let f_constr = constr >>| fun c -> PF_Constr c

let simple_formula = f_bot <|> f_top <|> f_constr <|> f_var

let f_and formula =
  sep_by2 (whitespace *> wedge <* whitespace) (simple_formula <|> parenthesized formula)
  >>| fun fs -> PF_And fs

let f_or formula =
  sep_by2 (whitespace *> vee <* whitespace) (simple_formula <|> parenthesized formula)
  >>| fun fs -> PF_Or fs

let f_impl formula =
  let* f1 = simple_formula <|> parenthesized formula in
  let* _ = whitespace *> double_arrow <* whitespace in
  let* f2 = formula in
  return $ PF_Impl (f1, f2)

let f_forall formula =
  let* x, k = forall (typed_op identifier pvar_kind) in
  match k with
  | Some PQ_Atom            -> formula >>| fun f -> PF_ForallAtom (x, f)
  | Some PQ_Term            -> formula >>| fun f -> PF_ForallTerm (x, f)
  | Some (PQ_Kind _) | None -> raise $ quantifier_without_kind_annotation "Forall" x

let f_exists formula =
  let* x, k = exists (typed_op identifier pvar_kind) in
  match k with
  | Some PQ_Atom            -> formula >>| fun f -> PF_ExistsAtom (x, f)
  | Some PQ_Term            -> formula >>| fun f -> PF_ExistsTerm (x, f)
  | Some (PQ_Kind _) | None -> raise $ quantifier_without_kind_annotation "Exists" x

let f_constrand formula =
  let* c = bracketed constr in
  let* _ = whitespace *> wedge <* whitespace in
  let* f = formula in
  return $ PF_ConstrAnd (c, f)

let f_constrimpl formula =
  let* c = bracketed constr in
  let* _ = whitespace *> double_arrow <* whitespace in
  let* f = formula in
  return $ PF_ConstrImpl (c, f)

let f_fun formula =
  let* _ = string "fun" <* whitespace1 in
  let* x, k = typed_op identifier pvar_kind in
  let* _ = whitespace *> arrow <* whitespace in
  match k with
  | Some PQ_Atom     -> formula >>| fun f -> PF_FunAtom (x, f)
  | Some PQ_Term     -> formula >>| fun f -> PF_FunTerm (x, f)
  | Some (PQ_Kind k) -> formula >>| fun f -> PF_Fun (x, k, f)
  | None             ->
      raise
      $ ParserException
          (Printf.sprintf
             "Functions must be used with type annotation, like 'fun x : k -> ...' where 'k' is \
              'atom', 'term' or kind" )

type pf_app_arg = PFA_Identfier of string | PFA_Term of pterm | PFA_Formula of pformula

let f_app formula =
  let app_identifier = identifier >>| fun x -> PFA_Identfier x
  and app_term = braced term >>| fun t -> PFA_Term t
  and app_formula = simple_formula <|> parenthesized formula >>| fun f -> PFA_Formula f in
  let* f = simple_formula <|> parenthesized formula in
  let* args = many1 (whitespace1 *> (app_identifier <|> app_term <|> app_formula)) in
  let apply f = function
    | PFA_Identfier x -> PF_AppIdentfier (f, x)
    | PFA_Term t      -> PF_AppTerm (f, t)
    | PFA_Formula f'  -> PF_App (f, f')
  in
  return $ List.fold_left apply f args

let formula =
  let formula' formula =
    f_and formula <|> f_or formula <|> f_impl formula <|> f_forall formula <|> f_exists formula
    <|> f_constrand formula <|> f_constrimpl formula <|> f_fun formula <|> f_app formula
    <|> simple_formula <|> parenthesized formula
  in
  fix formula'