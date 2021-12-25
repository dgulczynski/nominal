open Types
open Common

module SolverEnv = struct
  type atom_assumption = AFresh of atom * var | ANeq of atom * atom

  type t = atom_assumption list

  let empty = []

  let add_fresh gamma a x = AFresh (a, x) :: gamma

  let add_neq gamma a a' = if a = a' then None else Some (ANeq (a, a') :: gamma)

  let is_neq gamma a1 a2 =
    List.exists
      (function
        | ANeq (b1, b2) -> (b1 = a1 && b2 = a2) || (b1 = a2 && b2 = a1)
        | AFresh _      -> false )
      gamma

  let is_fresh gamma a x = List.mem (AFresh (a, x)) gamma

  let add_constr gamma = function
    | ANeq (a1, a2) -> add_neq gamma a1 a2
    | AFresh (a, v) -> Some (add_fresh gamma a v)

  let subst_atom_constr a b = function
    | ANeq (a1, a2) -> ANeq (sub a b a1, sub a b a2)
    | AFresh (c, v) -> AFresh (sub a b c, v)

  let subst_var_constr x t = function
    | AFresh (a, x') when x = x' ->
        List.map (fun z -> AFresh (a, z)) (free_vars_of_term t)
    | c -> [c]

  let subst_atom gamma a b =
    List.fold_left
      (fun env constr -> Option.bind env (flip add_constr $ subst_atom_constr a b constr))
      (Some empty) gamma

  let subst_var gamma x t =
    List.fold_left
      (fun env constr -> List.fold_left (flip List.cons) env (subst_var_constr x t constr))
      empty gamma

  let string_of gamma =
    List.fold_right
      (fun g str ->
        str
        ^ Printing.string_of_constr
            ( match g with
            | AFresh (a, v) -> Fresh (a, Var {perm= []; symb= v})
            | ANeq (a, b)   -> AtomNeq (a, {perm= []; symb= b}) )
        ^ "," )
      gamma ""
end
