open Types
open Permutation

val ( $ ) : ('a -> 'b) -> 'a -> 'b

val ( >> ) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

val permute_term : atom permutation -> term -> term

val const : 'a -> 'b -> 'a

val find_first : ('a -> bool) -> 'a list -> 'a option * 'a list

val sub : 'a -> 'a -> 'a -> 'a

val subst_atom : atom -> atom -> term -> term

val subst_var : var -> term -> term -> term

val subst_atom_constr : atom -> atom -> constr -> constr
