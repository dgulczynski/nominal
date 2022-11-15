open Types
open Common
open Printing

type proof =
  | P_Ax      of judgement
  | P_Intro   of judgement * proof
  | P_Apply   of judgement * proof * proof
  | P_ExFalso of judgement * proof

and proof_env = formula list

and judgement = proof_env * formula

let label = function
  | P_Ax (_, f) | P_Intro ((_, f), _) | P_Apply ((_, f), _, _) | P_ExFalso ((_, f), _) -> f

let env = function
  | P_Ax (e, _) | P_Intro ((e, _), _) | P_Apply ((e, _), _, _) | P_ExFalso ((e, _), _) -> e

let judgement proof = (env proof, label proof)

let equiv f1 f2 = f1 = f2

let ( === ) = equiv

let env_remove env f = List.filter (fun f' -> not (f === f')) env

let env_union e1 e2 = List.merge compare e1 e2

let env_add name formula = List.merge compare [(name, formula)]

let by_assumption f = P_Ax ([f], f)

let imp_i f p =
  let f' = label p in
  let env = env_remove (env p) f in
  P_Intro ((env, F_Impl (f, f')), p)

let imp_e p1 p2 =
  match (label p1, label p2) with
  | F_Impl (f2', f), f2 when f2 === f2' -> P_Apply ((env_union (env p1) (env p2), f), p1, p2)
  | f1, f2 ->
      failwith
      $ Printf.sprintf "%s is not an implication with hypothesis %s" (string_of_formula f1)
          (string_of_formula f2)

let bot_e f p =
  match label p with
  | F_Bot -> P_ExFalso ((env p, f), p)
  | f'    -> failwith
             $ Printf.sprintf "%s is not %s" (string_of_formula f') (string_of_formula F_Bot)
