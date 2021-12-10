type 'a permutation = 'a swap list

and 'a swap = ('a, 'a) permuted * ('a, 'a) permuted

and ('a, 'x) permuted = Just of 'x | Permuted of 'a permutation * 'x

let decons = function [] -> None | x :: xs -> Some (x, xs)

let permute pi x =
  match (pi, x) with
  | [], x                 -> x
  | pi, Just x            -> Permuted (pi, x)
  | pi, Permuted (pi', a) -> Permuted (pi' @ pi, a)

let reverse = List.rev

let rec free_vars_of = function [] -> [] | (a, b) :: pi -> a :: b :: free_vars_of pi
