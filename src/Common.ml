open Types
open Permutation

let ( $ ) f x = f x

let ( >> ) f g x = f (g x)

let rec permute_term (pi : atom permutation) = function
  | Atom a       -> Atom (permute pi a)
  | Var x        -> Var (permute pi x)
  | Lam (a, t)   -> Lam (permute pi a, permute_term pi t)
  | App (t1, t2) -> App (permute_term pi t1, permute_term pi t2)
  | Fun _ as t   -> t
