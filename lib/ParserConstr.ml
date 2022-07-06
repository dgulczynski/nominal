open Common
open Angstrom
open ParserTypes
open ParserCommon
open ParserTerm

let constr =
  let c_fresh =
    let* a, t = binop atom "#" term in
    return $ PC_Fresh (a, t)
  and c_eq =
    let* t1, t2 = binop term "=" term in
    return $ PC_Eq (t1, t2)
  and c_shape =
    let* t1, t2 = binop term "=~" term in
    return $ PC_Shape (t1, t2)
  and c_subshape =
    let* t1, t2 = binop term "<" term in
    return $ PC_Subshape (t1, t2)
  and c_atomneq =
    let* alpha1, alpha2 = binop (permuted atom) "=/=" (permuted atom) in
    return $ PC_AtomNeq (alpha1, alpha2)
  in
  c_fresh <|> c_eq <|> c_shape <|> c_subshape <|> c_atomneq