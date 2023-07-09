open Prelude
open Angstrom
open ParserTypes
open ParserCommon
open ParserTerm

let constr =
  let c_fresh =
    let* a, t = binop identifier "#" term in
    return $ PC_Fresh (a, t)
  and c_eq =
    let* t1, t2 = binop term "=" term in
    return $ PC_Eq (t1, t2)
  and c_shape =
    let* t1, t2 = binop term "~" term in
    return $ PC_Shape (t1, t2)
  and c_subshape =
    let* t1, t2 = binop term "<" term in
    return $ PC_Subshape (t1, t2)
  and c_atomneq =
    let* alpha1, alpha2 = binop (permuted identifier) "=/=" (permuted identifier) in
    return $ PC_AtomNeq (alpha1, alpha2)
  and c_symbol =
    let* _ = string "symbol" *> whitespace in
    let* t = term in
    return $ PC_Symbol t
  in
  parens_op $ c_fresh <|> c_eq <|> c_shape <|> c_subshape <|> c_atomneq <|> c_symbol
