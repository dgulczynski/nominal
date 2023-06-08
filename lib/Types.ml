open Permutation
open Prelude

type name_internal = int

type atom = A of name_internal

type var = V of name_internal

type permuted_atom = (atom, atom) permuted

type permuted_var = (atom, var) permuted

type term =
  | T_Var of permuted_var
  | T_Atom of permuted_atom
  | T_Lam of permuted_atom * term
  | T_App of term * term
  | T_Fun of string

let atom' a = T_Atom a

let atom = atom' % pure

let var' x = T_Var x

let var = var' % pure

let lam a e = T_Lam (a, e)

let app e1 e2 = T_App (e1, e2)

let symb f = T_Fun f

type shape = S_Var of var | S_Atom | S_Lam of shape | S_App of shape * shape | S_Fun of string

type constr =
  | C_Fresh of atom * term
  | C_Eq of term * term
  | C_Shape of term * term
  | C_Subshape of term * term
  | C_AtomEq of atom * permuted_atom
  | C_AtomNeq of atom * permuted_atom
  | C_Symbol of term

let ( #: ) a t = C_Fresh (a, t)

let ( =: ) t1 t2 = C_Eq (t1, t2)

let ( =~: ) t1 t2 = C_Shape (t1, t2)

let ( <: ) t1 t2 = C_Subshape (t1, t2)

let ( ==: ) a alpha = C_AtomEq (a, alpha)

let ( =/=: ) a alpha = C_AtomNeq (a, alpha)

let symbol t = C_Symbol t

type atom_binder = A_Bind of string * atom

type var_binder = V_Bind of string * var

type kind =
  | K_Prop
  | K_Arrow of kind * kind
  | K_ForallTerm of var_binder * kind
  | K_ForallAtom of atom_binder * kind
  | K_Constr of constr * kind

type fvar = FV of name_internal

type fvar_binder = FV_Bind of string * name_internal * kind

type formula =
  | F_Bot
  | F_Top
  | F_Constr of constr
  | F_And of (string * formula) list
  | F_Or of (string * formula) list
  | F_Impl of formula * formula
  | F_ForallTerm of var_binder * formula
  | F_ForallAtom of atom_binder * formula
  | F_ExistsTerm of var_binder * formula
  | F_ExistsAtom of atom_binder * formula
  | F_ConstrAnd of constr * formula
  | F_ConstrImpl of constr * formula
  | F_Var of fvar
  | F_Fun of fvar_binder * formula
  | F_App of formula * formula
  | F_FunTerm of var_binder * formula
  | F_AppTerm of formula * term
  | F_FunAtom of atom_binder * formula
  | F_AppAtom of formula * permuted_atom
  | F_Fix of fvar_binder * var_binder * kind * formula

let fvar x = F_Var (FV x)

type binder_kind = K_Atom of name_internal | K_Var of name_internal | K_FVar of name_internal * kind | K_Func

type binder = Bind of string * binder_kind

type bound_env = binder list

let binder_name = function
  | Bind (name, _) -> name

let binder_kind = function
  | Bind (_, kind) -> kind

let binder_rep = function
  | Bind (_, K_Atom i) | Bind (_, K_Var i) | Bind (_, K_FVar (i, _)) -> Some i
  | Bind (_, K_Func) -> None

let get_bind_opt name env = binder_kind <$> List.find_opt (( = ) name % binder_name) env

let fresh_generator ?(start = 0) =
  let counter = ref (start - 1) in
  fun () -> incr counter ; !counter

let fresh = fresh_generator ~start:0

let fresh_atom = (fun a -> A a) % fresh

let fresh_var = (fun x -> V x) % fresh

let fresh_fvar = (fun x -> FV x) % fresh

let rec shape_of_term = function
  | T_Var {symb= x; _} -> S_Var x
  | T_Atom _ -> S_Atom
  | T_Lam (_, t) -> S_Lam (shape_of_term t)
  | T_App (t1, t2) -> S_App (shape_of_term t1, shape_of_term t2)
  | T_Fun f -> S_Fun f

let rec permute_term (pi : atom permutation) = function
  | T_Atom a -> T_Atom (permute pi a)
  | T_Var x -> T_Var (permute pi x)
  | T_Lam (a, t) -> T_Lam (permute pi a, permute_term pi t)
  | T_App (t1, t2) -> T_App (permute_term pi t1, permute_term pi t2)
  | T_Fun _ as t -> t
