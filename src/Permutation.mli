type 'a permutation = 'a swap list

and 'a swap = ('a, 'a) permuted * ('a, 'a) permuted

and ('a, 'x) permuted = Just of 'x | Permuted of 'a permutation * 'x

val decons : 'a permutation -> ('a swap * 'a permutation) option

val permute : 'a permutation -> ('a, 'b) permuted -> ('a, 'b) permuted

val reverse : 'a permutation -> 'a permutation

val free_vars_of : 'a permutation -> ('a, 'a) permuted list
