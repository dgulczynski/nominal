type 'a permutation = 'a swap list

and 'a swap = ('a, 'a) permuted * ('a, 'a) permuted

and ('a, 'x) permuted = {perm: 'a permutation; symb: 'x}

let permute pi {perm; symb} = {perm= pi @ perm; symb}

let reverse = List.rev

let free_vars_of pi = List.fold_left (fun acc (a, b) -> a :: b :: acc) [] pi

let inner_swap = function [] -> None | swap :: rest -> Some (swap, rest)

let rec outer_swap = function
  | []      -> None
  | [swap]  -> Some (swap, [])
  | p :: ps -> Option.map (fun (s, ps) -> (s, p :: ps)) (outer_swap ps)

let pure x = {perm= []; symb= x}
