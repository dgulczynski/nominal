type 'a permutation = 'a swap list

and 'a swap = ('a, 'a) permuted * ('a, 'a) permuted

and ('a, 'x) permuted = {perm: 'a permutation; symb: 'x}

val pure : 'b -> ('a, 'b) permuted

val permute : 'a permutation -> ('a, 'b) permuted -> ('a, 'b) permuted

val reverse : 'a permutation -> 'a permutation

val free_vars_of : 'a permutation -> ('a, 'a) permuted list

val outer_swap : 'a permutation -> ('a swap * 'a permutation) option
(** short-hand getter for permutations: [outer_swap [] = None], [outer_swap ((x1, x2) :: xs) = Some
    ((x1, x2), xs)] *)

val inner_swap : 'a permutation -> ('a swap * 'a permutation) option
(** short-hand getter for permutations: [inner_swap [] = None], [inner_swap (xs @ [(x1, x2)]) = Some
    ((x1, x2), xs)] *)
