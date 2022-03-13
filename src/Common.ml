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

let to_option a test = if test then Some a else None

let rec find_first test = function
  | [] -> (None, [])
  | x :: xs when test x -> (Some x, xs)
  | x :: xs ->
      let found, rest = find_first test xs in
      (found, x :: rest)

let rec permute_term (pi : atom permutation) = function
  | T_Atom a       -> T_Atom (permute pi a)
  | T_Var x        -> T_Var (permute pi x)
  | T_Lam (a, t)   -> T_Lam (permute pi a, permute_term pi t)
  | T_App (t1, t2) -> T_App (permute_term pi t1, permute_term pi t2)
  | T_Fun _ as t   -> t

let rec occurs_check x = function
  | T_Var {perm= _; symb= x'} -> x' = x
  | T_Lam (_, t)              -> occurs_check x t
  | T_App (t1, t2)            -> occurs_check x t1 || occurs_check x t2
  | T_Atom _ | T_Fun _        -> false

let rec free_vars_of_term = function
  | T_Var {perm= _; symb= x} -> [x]
  | T_Lam (_, t)             -> free_vars_of_term t
  | T_App (t1, t2)           -> free_vars_of_term t1 @ free_vars_of_term t2
  | T_Fun _ | T_Atom _       -> []

let var x = T_Var (pure x)
