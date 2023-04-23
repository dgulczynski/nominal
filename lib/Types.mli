open Permutation

(**  Int is the internal representation of variables, but the user shall think it is simply a name. *)
type name_internal = int

(** [atom] is a term-level variable *)
type atom = A of name_internal

(** [var] is a meta-level variable *)
type var = V of name_internal

(** [permuted_atom] is an [atom] permuted with [atom permutation] *)
type permuted_atom = (atom, atom) permuted

(** [permuted_var] is a [var] permuted with [atom permutation] *)
type permuted_var = (atom, var) permuted

type term =
  | T_Var  of permuted_var
  | T_Atom of permuted_atom
  | T_Lam  of permuted_atom * term
  | T_App  of term * term
  | T_Fun  of string

val atom : atom -> term
(** [atom a = T_Atom (pure a)] *)

val var : var -> term
(** [var x = T_Var (pure x)] *)

type shape = S_Var of var | S_Atom | S_Lam of shape | S_App of shape * shape | S_Fun of string

(** [constr] is constraint that the [Solver] solves. [ G; C |- c ] means that in [SolverEnv] [G]
    with assumptions [C] (of type [constr list]) the goal constraint [c] ([constr]) is satisfied. *)
type constr =
  | C_Fresh    of atom * term
  | C_Eq       of term * term
  | C_Shape    of term * term
  | C_Subshape of term * term
  | C_AtomEq   of atom * permuted_atom
  | C_AtomNeq  of atom * permuted_atom
  | C_Symbol   of term

val ( #: ) : atom -> term -> constr
(** [ a #: t] is a [constr] that [a] is fresh in [t] *)

val ( =: ) : term -> term -> constr
(** [ t1 =: t2] is a [constr] that [t1] is equal to [t2] *)

val ( =~: ) : term -> term -> constr
(** [ t1 =~: t2] is a [constr] that [t1] have same shape [t2] *)

val ( <: ) : term -> term -> constr
(** [ t1 <: t2] is a [constr] that shape of [t1] is a sub-shape of [t2]'s shape *)

val ( ==: ) : atom -> permuted_atom -> constr
(** [ a ==: α] is a [constr] that [a] is equal to [α] (same as [T_Atom (pure a) =: T_Atom α])*)

val ( =/=: ) : atom -> permuted_atom -> constr
(** [ a =/=: α] is a [constr] that [a] is not equal to [α] (same as [ a #: T_Atom α])*)

val symbol : term -> constr
(** [symbol t] is a [constr] that [t] is some functional symbol *)

type atom_binder = A_Bind of string * atom

type var_binder = V_Bind of string * var

(** [kind] is the type of [formula]s*)
type kind =
  | K_Prop
  | K_Arrow      of kind * kind
  | K_ForallTerm of var_binder * kind
  | K_ForallAtom of atom_binder * kind
  | K_Constr     of constr * kind

(** [fvar] is a formula-level variable *)
type fvar = FV of name_internal

type fvar_binder = FV_Bind of string * name_internal * kind

type formula =
  | F_Bot
  | F_Top
  | F_Constr     of constr
  | F_And        of (string * formula) list
  | F_Or         of (string * formula) list
  | F_Impl       of formula * formula
  | F_ForallTerm of var_binder * formula
  | F_ForallAtom of atom_binder * formula
  | F_ExistsTerm of var_binder * formula
  | F_ExistsAtom of atom_binder * formula
  | F_ConstrAnd  of constr * formula
  | F_ConstrImpl of constr * formula
  | F_Var        of fvar
  | F_Fun        of fvar_binder * formula
  | F_App        of formula * formula
  | F_FunTerm    of var_binder * formula
  | F_AppTerm    of formula * term
  | F_FunAtom    of atom_binder * formula
  | F_AppAtom    of formula * permuted_atom
  | F_Fix        of fvar_binder * var_binder * kind * formula

val fvar : int -> formula
(** [fvar x = F_Var (FV x)] *)

type binder_kind =
  | K_Atom of name_internal
  | K_Var  of name_internal
  | K_FVar of name_internal * kind
  | K_Func

type binder = Bind of string * binder_kind

type bound_env = binder list

val binder_name : binder -> string

val binder_kind : binder -> binder_kind

val binder_rep : binder -> name_internal option

val get_bind_opt : string -> bound_env -> binder_kind option

val fresh : unit -> name_internal

val fresh_atom : unit -> atom

val fresh_var : unit -> var

val fresh_fvar : unit -> fvar
