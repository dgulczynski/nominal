open Common
open ProofException
open Types

let to_constr_op = function
  | F_Constr c -> Some c
  | _          -> None

let to_constr f =
  match to_constr_op f with
  | Some c -> c
  | None   -> raise $ not_a_constraint f

let premise = function
  | F_Impl (p, _)       -> p
  | F_ConstrImpl (c, _) -> F_Constr c
  | f                   -> raise $ not_an_implication f

let conclusion = function
  | F_Impl (_, c) | F_ConstrImpl (_, c) -> c
  | f -> raise $ not_an_implication f

let equiv (f1 : formula) (f2 : formula) = f1 = f2

let ( === ) = equiv

let ( =/= ) = not %% ( === )
