open Prelude
open Angstrom
open ParserCommon
open ParserTypes

let term : pterm t =
  let t_identifier =
    let* x = permuted identifier in
    return $ PT_Identifier x
  in
  let t_lam term =
    let* a = permuted identifier in
    let* _ = whitespace *> char '.' *> whitespace in
    let* t = term in
    return $ PT_Lam (a, t)
  and t_app term =
    let term = parens_op t_identifier <|> parenthesized term in
    let* t = term in
    let* ts = many1 (whitespace1 *> term) in
    return $ List.fold_left (fun e e' -> PT_App (e, e')) t ts
  in
  let t_permuted term =
    let* pt = permuted (parenthesized term) in
    return $ PT_Permuted pt
  in
  let pterm' pterm = t_lam pterm <|> t_app pterm <|> parenthesized pterm <|> t_identifier <|> t_permuted pterm in
  fix pterm'
