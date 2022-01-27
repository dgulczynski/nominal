open Types

module KindCheckerEnv = struct
  type kind_assumption = Constr of constr

  type t = kind_assumption list

  let empty = []

  let add_constr gamma c = Constr c :: gamma

  let mem_constr gamma c = List.mem (Constr c) gamma

  let constraints_of = List.map (function Constr c -> c)

  let string_of_kind_assumption = function
    | Constr c -> Printing.string_of_constr c

  let string_of = Printing.string_of_list string_of_kind_assumption
end
