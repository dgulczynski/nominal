open Types
open Printing
open ProofCommon

type 'a env

val assumptions : 'a env -> 'a list

val identifiers : 'a env -> identifier_env

val constraints : 'a env -> constr list

val mapping : 'a env -> mapping

val env : identifier_env -> constr list -> 'a list -> mapping -> 'a env
(** For any [e : env] it should be that [e = env (identifiers e) (constraints e) (assumptions e) (mapping e)] *)

val empty : 'a env

val singleton : 'a -> 'a env

val union : 'a env -> 'a env -> 'a env

val add_fvar : string -> int -> kind -> 'a env -> 'a env

val add_atom : string -> 'a env -> 'a env

val add_var : string -> 'a env -> 'a env

val remove_identifier : string -> 'a env -> 'a env

val add_constr : constr -> 'a env -> 'a env

val add_assumption : 'a -> 'a env -> 'a env

val map_assumptions : ('a -> 'b) -> 'a env -> 'b env

val lookup_assumption : ('a -> bool) -> 'a env -> 'a option

val lookup_identifier : string -> 'a env -> identifier option

val remove_assumptions : ('a -> bool) -> 'a env -> 'a env

val remove_constraints : (constr -> bool) -> 'a env -> 'a env

val remove_identifiers : (identifier -> bool) -> 'a env -> 'a env

val remove_assumptions_equiv_to : ('a -> formula) -> formula -> 'a env -> 'a env

val parse_formula : 'a env -> string -> formula

val parse_mapping : identifier_env -> constr list -> 'a list -> (string * string) list -> 'a env

val kind_checker_env : 'a env -> KindCheckerEnv.t

val kind_infer : 'a env -> formula -> kind option

val find_bind : ('a -> formula) -> string -> 'a env -> formula option

val all_identifiers : 'a env -> identifier_env

val on_assumptions : ('a list -> 'b list) -> 'a env -> 'b env

val set_mapping : mapping -> 'a env -> 'a env

val ( === ) : formula -> formula -> 'a env -> bool

val pp_print_env : 'a printer -> 'a env printer
