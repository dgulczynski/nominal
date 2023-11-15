open Types
open ProofCommon

type 'a env

val assumptions : 'a env -> 'a list

val identifiers : 'a env -> bound_env

val constraints : 'a env -> constr list

val mapping : 'a env -> mapping

val to_formula : 'a env -> 'a -> formula

val env : bound_env -> constr list -> 'a list -> mapping -> ('a -> formula) -> 'a env
(** For any [e : env] it should be that [e = env (identifiers e) (constraints e) (assumptions e) (mapping e) (to_formula e)] *)

val empty : ('a -> formula) -> 'a env

val singleton : 'a -> ('a -> formula) -> 'a env

val union : 'a env -> 'a env -> 'a env

val add_identifier : binder -> 'a env -> 'a env

val add_fvar : fvar_binder -> 'a env -> 'a env

val add_atom : atom_binder -> 'a env -> 'a env

val add_var : var_binder -> 'a env -> 'a env

val remove_identifier : name_internal -> 'a env -> 'a env

val add_constr : constr -> 'a env -> 'a env

val add_assm : 'a -> 'a env -> 'a env

val map_assms : ('a -> 'b) -> ('b -> formula) -> 'a env -> 'b env

val lookup_assm : ('a -> bool) -> 'a env -> 'a option

val lookup_identifier : string -> 'a env -> binder option

val map_constraints : (constr -> constr) -> 'a env -> 'a env

val remove_assms : ('a -> bool) -> 'a env -> 'a env

val remove_constraints : (constr -> bool) -> 'a env -> 'a env

val remove_identifiers : (binder -> bool) -> 'a env -> 'a env

val parse_formula : 'a env -> string -> formula

val parse_mapping : bound_env -> constr list -> 'a list -> ('a -> formula) -> (string * string) list -> 'a env

val kind_checker_env : 'a env -> KindCheckerEnv.t

val kind_check : 'a env -> kind -> formula -> bool

val kind_check_throw : 'a env -> kind -> formula -> unit

val kind_infer : 'a env -> formula -> kind option

val find_bind : string -> 'a env -> formula option

val remove_var : string -> 'a env -> 'a env

val all_identifiers : 'a env -> bound_env

val set_mapping : mapping -> 'a env -> 'a env

val subst_var : (var -> term -> 'a -> 'a) -> var -> term -> 'a env -> 'a env

val subst_atom : (atom -> permuted_atom -> 'a -> 'a) -> atom -> permuted_atom -> 'a env -> 'a env

val solver_env : 'a env -> constr list

val raise_in_env : 'a env -> (bound_env -> exn) -> 'b
