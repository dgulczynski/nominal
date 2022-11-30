open Common
open ProofException
open Types

let premise = function
  | F_Impl (p, _) -> p
  | f             -> raise $ not_an_implication f

let conclusion = function
  | F_Impl (_, c) -> c
  | f             -> raise $ not_an_implication f

let equiv (f1 : formula) (f2 : formula) = f1 = f2

let ( === ) = equiv

let ( =/= ) = not %% ( === )
