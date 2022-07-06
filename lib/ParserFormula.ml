open Common
open Angstrom
open ParserTypes
open ParserCommon
open ParserTerm
open ParserKind
open ParserConstr

let typed x t = x >>= fun x -> whitespace *> string ":" *> whitespace *> t >>| fun t -> (x, t)

let f_bot = string "false" <|> string "⊥" >>| const PF_Bot

let f_top = string "true" <|> string "⊤" >>| const PF_Top

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

type pformula_kind = PK_Atom | PK_Term | PK_Kind of pkind

let formula_kind =
  let atom = string_ci "atom" >>| const PK_Atom
  and term = string_ci "term" >>| const PK_Term
  and formula = kind >>| fun k -> PK_Kind k in
  atom <|> term <|> formula

let f_quantifier quantifier formula =
  let* x, k = quantifier (typed identifier formula_kind) in
  let* f = formula in
  return (x, k, f)

let f_forall formula =
  let* x, k, f = f_quantifier forall formula in
  match k with
  | PK_Atom -> return $ PF_ForallAtom (x, f)
  | PK_Term -> return $ PF_ForallTerm (x, f)
  | _       -> failwith "Forall quantifier must be used with ': atom' or ': term' kind annotation"

let f_exists formula =
  let* x, k, f = f_quantifier exists formula in
  match k with
  | PK_Atom -> return $ PF_ExistsAtom (x, f)
  | PK_Term -> return $ PF_ExistsTerm (x, f)
  | _       -> failwith "Exists quantifier must be used with ': atom' or ': term' kind annotation"

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
  let* x, k = typed identifier formula_kind in
  let* _ = whitespace *> arrow <* whitespace in
  let* f = formula in
  match k with
  | PK_Atom   -> return $ PF_FunAtom (x, f)
  | PK_Term   -> return $ PF_FunTerm (x, f)
  | PK_Kind k -> return $ PF_Fun (x, k, f)

type pf_app_arg =
  | PF_AppArgIdentfier of string
  | PF_AppArgTerm      of pterm
  | PF_AppArgFormula   of pformula

let f_app formula =
  let app_identifier = identifier >>| fun x -> PF_AppArgIdentfier x
  and app_term = parenthesized term >>| fun t -> PF_AppArgTerm t
  and app_formula = simple_formula <|> parenthesized formula >>| fun f -> PF_AppArgFormula f in
  let* f = simple_formula <|> parenthesized formula in
  let* args = many1 (whitespace1 *> (app_identifier <|> app_term <|> app_formula)) in
  let apply f = function
    | PF_AppArgIdentfier x -> PF_AppIdentfier (f, x)
    | PF_AppArgTerm t      -> PF_AppTerm (f, t)
    | PF_AppArgFormula f'  -> PF_App (f, f')
  in
  return $ List.fold_left apply f args

let formula =
  let formula' formula =
    f_and formula <|> f_or formula <|> f_impl formula <|> f_forall formula <|> f_exists formula
    <|> f_constrand formula <|> f_constrimpl formula <|> f_fun formula <|> f_app formula
    <|> simple_formula <|> parenthesized formula
  in
  fix formula'
