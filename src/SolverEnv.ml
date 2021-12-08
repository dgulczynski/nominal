open Types
open Common

module SolverEnv = struct
  type atom_assumption = AFresh of atom * var | ANeq of atom * atom

  type t = {gamma: atom_assumption list; assumptions: constr list}

  let add_to_gamma {gamma; assumptions} g = {gamma= g :: gamma; assumptions}

  let empty = {gamma= []; assumptions= []}

  let add_fresh env a x = add_to_gamma env $ AFresh (a, x)

  let add_neq env a a' =
    if a = a' then None else Some (add_to_gamma env $ ANeq (a, a'))

  let is_neq {gamma; _} a1 a2 =
    List.exists
      (function
        | ANeq (b1, b2) -> (b1 = a1 && b2 = a2) || (b1 = a2 && b2 = a1)
        | _             -> false )
      gamma

  let is_fresh {gamma; _} a x = List.mem (AFresh (a, x)) gamma
end
