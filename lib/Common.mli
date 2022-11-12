open Types
open Permutation

val ( $ ) : ('a -> 'b) -> 'a -> 'b

val ( % ) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

val ( <$> ) : ('a -> 'b) -> 'a option -> 'b option

val ( >>= ) : 'a option -> ('a -> 'b option) -> 'b option

val id : 'a -> 'a

val const : 'a -> 'b -> 'a

val const2 : 'a -> 'b -> 'c -> 'a

val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c

val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c

val hd_opt : 'a list -> 'a option

val pair_eq : 'a * 'a -> 'a * 'a -> bool
(** [pair_eq (x1, x2) (y1, y2) = (x1 = y1 && x2 = y2) || (x1 = y2 && x2 = y1)]*)

val to_option : 'a -> bool -> 'a option
(** cast ['a] to ['a option]: [to_option x true = Some x], [to_option _ false = None]*)

val find_first : ('a -> bool) -> 'a list -> 'a option * 'a list
(** [find_first p xs] returns first [x] s.t. [p x = true] (if it exists) and the remaining [xs] *)

val permute_term : atom permutation -> term -> term

val syntactic_occurs_check : var -> term -> bool

val free_vars_of_term : term -> var list

val atom : atom -> term
(** [atom a = T_Atom (pure a)] *)

val var : var -> term
(** [var x = T_Var (pure x)] *)

val fvar : fvar -> formula
(** [fvar x = F_Var x] *)

val fresh_var : unit -> var

val fresh_atom : unit -> atom

val fresh_fvar : unit -> fvar

val shape_of_term : term -> shape

val term_of_shape : shape -> term * (var * var) list
(** [term_of_shape s] returns [t] (which shape is the same as [s] up to alpha-equivalence) and [vs]
    (mapping from the [s] variables to generated fresh variables of [t]) *)
