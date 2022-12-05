open Types
open Printing

type 'a env

val assumptions : 'a env -> 'a list

val identifiers : 'a env -> identifier_env

val constraints : 'a env -> constr list

val env : identifier_env -> constr list -> 'a list -> 'a env
(** For any [e : env] it should be that [e = env (identifiers e) (constraints e) (assumptions e)] *)

val empty : 'a env

val singleton : 'a -> 'a env

val union : 'a env -> 'a env -> 'a env

val add_fvar : string -> int -> kind -> 'a env -> 'a env

val add_constr : constr -> 'a env -> 'a env

val add_assumption : 'a -> 'a env -> 'a env

val map_assumptions : ('a -> 'b) -> 'a env -> 'b env

val lookup_assumption : ('a -> bool) -> 'a env -> 'a option

val remove_assumptions : ('a -> bool) -> 'a env -> 'a env

val pp_print_env : 'a printer -> 'a env printer
