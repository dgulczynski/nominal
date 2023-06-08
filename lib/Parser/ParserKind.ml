open Prelude
open Angstrom
open ParserTypes
open ParserCommon
open ParserConstr

let pvar_kind' kind =
  let atom = string_ci "atom" >>| const PQ_Atom
  and term = string_ci "term" >>| const PQ_Term
  and formula = kind >>| fun k -> PQ_Kind k in
  atom <|> term <|> formula

let kind =
  let k_prop = string_ci "Prop" <|> string "*" >>| const PK_Prop in
  let k_forall kind =
    let* xs, xk = forall (typed_op (list_of' identifier) $ pvar_kind' kind) in
    match xk with
    | Some PQ_Atom -> kind >>| List.fold_right (fun x k -> PK_ForallAtom (x, k)) xs
    | Some PQ_Term -> kind >>| List.fold_right (fun x k -> PK_ForallTerm (x, k)) xs
    | Some (PQ_Kind _) | None -> raise % quantifier_without_kind_annotation "Forall" $ Printing.unwords xs
  and k_constr kind =
    let* cs = many1 (bracketed constr <* whitespace) in
    let* k = kind in
    return $ List.fold_right (fun c k -> PK_Constr (c, k)) cs k
  and k_arrow kind =
    let* k1 = k_prop <|> parenthesized kind in
    let* _ = whitespace *> arrow <* whitespace in
    let* k2 = kind in
    return $ PK_Arrow (k1, k2)
  in
  let kind' kind = k_arrow kind <|> k_prop <|> k_forall kind <|> k_constr kind <|> parenthesized kind in
  fix kind'

let pvar_kind = pvar_kind' kind
