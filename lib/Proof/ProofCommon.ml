open Common
open ProofException
open Types

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
