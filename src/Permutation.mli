type 'a permutation = 'a swap list

and 'a swap = ('a, 'a) permuted * ('a, 'a) permuted

and ('a, 'x) permuted = {perm: 'a permutation; symb: 'x}

val pure : 'b -> ('a, 'b) permuted

val permute : 'a permutation -> ('a, 'b) permuted -> ('a, 'b) permuted

val reverse : 'a permutation -> 'a permutation

val free_vars_of : 'a permutation -> ('a, 'a) permuted list

val inner_swap : 'a permutation -> ('a swap * 'a permutation) option

val outer_swap : 'a permutation -> ('a swap * 'a permutation) option
