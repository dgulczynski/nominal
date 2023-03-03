open Permutation

(** [atom] is a term-level variable *)
type atom = A of string

(** [var] is a meta-level variable *)
type var = V of string

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

(** [kind] is the type of [formula]s*)
type kind =
  | K_Prop
  | K_Arrow      of kind * kind
  | K_ForallTerm of var * kind
  | K_ForallAtom of atom * kind
  | K_Constr     of constr * kind

(**  Int is the internal representation of logical variables, but the user shall think it is simply a name. *)
type fvar_internal = int

(** [fvar] is a formula-level variable *)
type fvar = FV of fvar_internal

type fvar_binder = FV_Bind of string * fvar_internal * kind

type formula =
  | F_Bot
  | F_Top
  | F_Constr     of constr
  | F_And        of (string * formula) list
  | F_Or         of (string * formula) list
  | F_Impl       of formula * formula
  | F_ForallTerm of var * formula
  | F_ForallAtom of atom * formula
  | F_ExistsTerm of var * formula
  | F_ExistsAtom of atom * formula
  | F_ConstrAnd  of constr * formula
  | F_ConstrImpl of constr * formula
  | F_Var        of fvar
  | F_Fun        of fvar_binder * formula
  | F_App        of formula * formula
  | F_FunTerm    of var * formula
  | F_AppTerm    of formula * term
  | F_FunAtom    of atom * formula
  | F_AppAtom    of formula * atom
  | F_Fix        of fvar_binder * var * kind * formula

type identifier_kind = K_Atom | K_Var | K_Func | K_FVar of fvar_internal * kind

type identifier = string * identifier_kind

type identifier_env = identifier list
