open Types
open Permutation

val ( $ ) : ('a -> 'b) -> 'a -> 'b

val ( >> ) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

val id : 'a -> 'a

val const : 'a -> 'b -> 'a

val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c

val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c

val hd_opt : 'a list -> 'a option

val find_first : ('a -> bool) -> 'a list -> 'a option * 'a list

val permute_term : atom permutation -> term -> term

val occurs_check : var -> term -> bool

val free_vars_of_term : term -> var list

val var : var -> term
