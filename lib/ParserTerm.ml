open Common
open Angstrom
open Types
open Permutation
open ParserCommon
open ParserTypes

let swap =
  let* a1 = char '(' *> identifier in
  let* _ = whitespace in
  let* a2 = identifier <* char ')' in
  return (pure (A a1), pure (A a2))

let permuted p =
  let* perm = many swap in
  let* symb = p in
  return {symb; perm}

let term : pterm t =
  let t_identifier = permuted identifier >>| fun x -> PT_Identifier x in
  let t_lam term =
    let* a = atom in
    let* _ = whitespace *> char '.' *> whitespace in
    let* t = term in
    return $ PT_Lam (a, t)
  and t_app term =
    let term = parens_op t_identifier <|> parenthesized term in
    let* t = term in
    let* ts = many1 (whitespace1 *> term) in
    return $ List.fold_left (fun e e' -> PT_App (e, e')) t ts
  in
  let pterm' pterm = t_lam pterm <|> t_app pterm <|> parenthesized pterm <|> t_identifier in
  fix pterm'
