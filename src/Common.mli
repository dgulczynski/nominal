open Types
open Permutation

val ( $ ) : ('a -> 'b) -> 'a -> 'b

val ( >> ) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

val permute_term : atom permutation -> term -> term
