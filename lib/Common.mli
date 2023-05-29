val ( $ ) : ('a -> 'b) -> 'a -> 'b

val ( <| ) : ('a -> 'b) -> 'a -> 'b

val ( % ) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

val ( %% ) : ('c -> 'd) -> ('a -> 'b -> 'c) -> 'a -> 'b -> 'd

val ( %> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
(** [f %> g] is reverse composition [(f %> g) x = g (f x)], useful for dividing proofs into parts *)

val ( <$> ) : ('a -> 'b) -> 'a option -> 'b option

val ( >>= ) : 'a option -> ('a -> 'b option) -> 'b option

val some : 'a -> 'a option

val none : 'a option

val id : 'a -> 'a

val const : 'a -> 'b -> 'a

val const2 : 'a -> 'b -> 'c -> 'a

val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c

val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c

val hd_opt : 'a list -> 'a option

val null : 'a list -> bool

val pair : 'a -> 'b -> 'a * 'b

val on_fst : ('a1 -> 'a2) -> 'a1 * 'b -> 'a2 * 'b

val on_snd : ('b1 -> 'b2) -> 'a * 'b1 -> 'a * 'b2

val pair_eq : ('a -> 'a -> bool) -> 'a * 'a -> 'a * 'a -> bool
(** [pair_eq (=) (x1, x2) (y1, y2) = (x1 = y1 && x2 = y2) || (x1 = y2 && x2 = y1)]*)

val to_option : 'a -> bool -> 'a option
(** cast ['a] to ['a option]: [to_option x true = Some x], [to_option _ false = None]*)

val find_first : ('a -> bool) -> 'a list -> 'a option * 'a list
(** [find_first p xs] returns first [x] s.t. [p x = true] (if it exists) and the remaining [xs] *)

val forall2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
(** [forall2] is like [List.for_all2] but returns [false] on lists of different length instead of throwing *)
