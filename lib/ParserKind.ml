open Common
open Angstrom
open ParserTypes
open ParserCommon
open ParserConstr

let kind =
  let k_prop = string "Prop" <|> string "*" >>| const PK_Prop in
  let k_forall kind =
    let* x = forall identifier in
    let* k = kind in
    return $ PK_Forall (x, k)
  and k_constr kind =
    let* cs = many1 (bracketed constr <* whitespace) in
    let* k = kind in
    return $ List.fold_right (fun c k -> PK_Constr (c, k)) cs k
  and k_arrow kind =
    let* k1 = k_prop <|> parenthesized kind in
    let* _ = whitespace *> double_arrow <* whitespace in
    let* k2 = kind in
    return $ PK_Arrow (k1, k2)
  in
  let kind' kind =
    k_arrow kind <|> k_prop <|> k_forall kind <|> k_constr kind <|> parenthesized kind
  in
  fix kind'
