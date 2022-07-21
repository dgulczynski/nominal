open Types
open Permutation

let ( $ ) f x = f x

let ( % ) f g x = f (g x)

let ( <$> ) = Option.map

let ( >>= ) = Option.bind

let flip f x y = f y x

let id x = x

let curry f x y = f (x, y)

let uncurry f (x, y) = f x y

let hd_opt = function
  | []     -> None
  | x :: _ -> Some x

let const x _ = x

let pair_eq (x1, x2) (y1, y2) = (x1 = y1 && x2 = y2) || (x1 = y2 && x2 = y1)

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

let rec syntactic_occurs_check x = function
  | T_Var {perm= _; symb= x'} -> x' = x
  | T_Lam (_, t)              -> syntactic_occurs_check x t
  | T_App (t1, t2)            -> syntactic_occurs_check x t1 || syntactic_occurs_check x t2
  | T_Atom _ | T_Fun _        -> false

let rec free_vars_of_term = function
  | T_Var {perm= _; symb= x} -> [x]
  | T_Lam (_, t)             -> free_vars_of_term t
  | T_App (t1, t2)           -> free_vars_of_term t1 @ free_vars_of_term t2
  | T_Fun _ | T_Atom _       -> []

let atom a = T_Atom (pure a)

let var x = T_Var (pure x)

let fresh_generator prefix =
  let counter = ref 0 in
  fun () ->
    counter := !counter + 1 ;
    prefix ^ string_of_int !counter

let fresh_var =
  let generate = fresh_generator "_x" in
  fun () -> V (generate ())

let fresh_atom =
  let generate = fresh_generator "_a" in
  fun () -> A (generate ())

let fresh_fvar =
  let generate = fresh_generator "_X" in
  fun () -> FV (generate ())

let rec shape_of_term = function
  | T_Var {symb= x; _} -> S_Var x
  | T_Atom _           -> S_Atom
  | T_Lam (_, t)       -> S_Lam (shape_of_term t)
  | T_App (t1, t2)     -> S_App (shape_of_term t1, shape_of_term t2)
  | T_Fun f            -> S_Fun f

let rec term_of_shape = function
  | S_Var x        ->
      let y = fresh_var () in
      (var y, [(x, y)])
  | S_Atom         -> (atom $ fresh_atom (), [])
  | S_Lam s        ->
      let t, vs = term_of_shape s in
      (T_Lam (pure $ fresh_atom (), t), vs)
  | S_App (s1, s2) ->
      let t1, vs1 = term_of_shape s1 and t2, vs2 = term_of_shape s2 in
      (T_App (t1, t2), vs1 @ vs2)
  | S_Fun f        -> (T_Fun f, [])