open Types

(** Similar to [constr] but uses [shape]s instead of terms for shape-related constraint *)
type solver_constr = private
  | SC_Fresh of atom * term
  | SC_Eq of term * term
  | SC_Shape of shape * shape
  | SC_Subshape of shape * shape
  | SC_AtomEq of atom * permuted_atom
  | SC_AtomNeq of atom * permuted_atom
  | SC_Symbol of shape

val ( #: ) : atom -> term -> solver_constr
(** [a #: t] is a [solver_constr] that [a] is fresh in [t] *)

val ( =: ) : term -> term -> solver_constr
(** [t1 =: t2] is a [solver_constr] that terms [t1] and [t2] are equal *)

val ( =~: ) : shape -> shape -> solver_constr
(** [t1 =~: t2] is a [solver_constr] that shapes [s1] and [s2] are equal *)

val ( <: ) : shape -> shape -> solver_constr
(** [s1 <: s2] is a [solver_constr] that [s1] is a sub-shape of [s2] *)

val ( ==: ) : atom -> permuted_atom -> solver_constr
(** [a ==: α] is a [solver_constr] that [a] is equal to [α] (same as [T_Atom (pure a) =: T_Atom α])*)

val ( =/=: ) : atom -> permuted_atom -> solver_constr
(** [a =/=: α] is a [solver_constr] that [a] is not equal to [α] (same as [ a #: T_Atom α])*)

val symbol : shape -> solver_constr
(** [symbol s] is a [solver_constr] that [s] has a shape of (unknown) symbol *)

val from_constr : constr -> solver_constr

val subst_atom_in_solver_constr : atom -> permuted_atom -> solver_constr -> solver_constr

val subst_var_in_solver_constr : var -> term -> solver_constr -> solver_constr
