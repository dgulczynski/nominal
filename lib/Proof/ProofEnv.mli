open Printing

type 'a env

val empty : 'a env

val singleton : 'a -> 'a env

val union : 'a env -> 'a env -> 'a env

val add : 'a -> 'a env -> 'a env

val map : ('a -> 'b) -> 'a env -> 'b env

val to_list : 'a env -> 'a list

val from_list : 'a list -> 'a env

val lookup : 'a env -> ('a -> bool) -> 'a option

val remove : 'a env -> ('a -> bool) -> 'a env

val pp_print_env : 'a printer -> 'a env printer
