type 'a permutation = 'a swap list

and 'a swap = ('a, 'a) permuted * ('a, 'a) permuted

and ('a, 'x) permuted = {perm: 'a permutation; symb: 'x}

val permute : 'a permutation -> ('a, 'b) permuted -> ('a, 'b) permuted

val reverse : 'a permutation -> 'a permutation

val free_vars_of : 'a permutation -> ('a, 'a) permuted list
