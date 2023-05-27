open Common
open ProofException
open Types

type specialized = SpecializedAtom of permuted_atom * formula | SpecializedTerm of term * formula

type formula_mapping = {bind: fvar_binder; body: formula}

type mapping = formula_mapping list

let to_constr_op = function
  | F_Constr c -> Some c
  | _ -> None

let to_constr f =
  match to_constr_op f with
  | Some c -> c
  | None -> raise $ not_a_constraint f

let premise = function
  | F_Impl (p, _) -> p
  | F_ConstrImpl (c, _) -> F_Constr c
  | f -> raise $ not_an_implication f

let conclusion = function
  | F_Impl (_, c) | F_ConstrImpl (_, c) -> c
  | f -> raise $ not_an_implication f

let disjuncts = function
  | F_Or fs -> fs
  | f -> raise $ not_a_disjunction f

let specialize on_forall_atom on_forall_term =
  let ( <$> ) g = function
    | SpecializedAtom (a, f) -> SpecializedAtom (a, g f)
    | SpecializedTerm (t, f) -> SpecializedTerm (t, g f)
  in
  let rec specialize' = function
    | F_ForallAtom (a, f) -> on_forall_atom a f
    | F_ForallTerm (x, f) -> on_forall_term x f
    | F_Impl (premise, f) -> (fun f -> F_Impl (premise, f)) <$> specialize' f
    | F_ConstrImpl (c, f) -> (fun f -> F_ConstrImpl (c, f)) <$> specialize' f
    | f -> raise $ cannot_specialize f
  in
  specialize'
