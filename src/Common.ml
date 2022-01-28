open Types
open Permutation

let ( $ ) f x = f x

let ( >> ) f g x = f (g x)

let flip f x y = f y x

let id x = x

let curry f x y = f (x, y)

let uncurry f (x, y) = f x y

let hd_opt = function
  | []     -> None
  | x :: _ -> Some x

let const x _ = x

let rec find_first test = function
  | [] -> (None, [])
  | x :: xs when test x -> (Some x, xs)
  | x :: xs ->
      let found, rest = find_first test xs in
      (found, x :: rest)

let rec permute_term (pi : atom permutation) = function
  | Atom a       -> Atom (permute pi a)
  | Var x        -> Var (permute pi x)
  | Lam (a, t)   -> Lam (permute pi a, permute_term pi t)
  | App (t1, t2) -> App (permute_term pi t1, permute_term pi t2)
  | Fun _ as t   -> t

let rec occurs_check x = function
  | Var {perm= _; symb= x'} -> x' = x
  | Lam (_, t)              -> occurs_check x t
  | App (t1, t2)            -> occurs_check x t1 || occurs_check x t2
  | Atom _ | Fun _          -> false

let rec free_vars_of_term = function
  | Var {perm= _; symb= x} -> [x]
  | Lam (_, t)             -> free_vars_of_term t
  | App (t1, t2)           -> free_vars_of_term t1 @ free_vars_of_term t2
  | Fun _ | Atom _         -> []
