open Common
open Format
open Printing
open Types

type 'a env = {identifiers: identifier_env; constraints: constr list; assumptions: 'a list}

let assumptions {assumptions; _} = assumptions

let identifiers {identifiers; _} = identifiers

let constraints {constraints; _} = constraints

let env identifiers constraints assumptions = {assumptions; constraints; identifiers}

let empty = env [] [] []

let singleton f = env [] [] [f]

let on_assumptions f {assumptions; identifiers; constraints} =
  {assumptions= f assumptions; identifiers; constraints}

let on_identifiers f {assumptions; identifiers; constraints} =
  {assumptions; identifiers= f identifiers; constraints}

let on_constraints f {assumptions; identifiers; constraints} =
  {assumptions; identifiers; constraints= f constraints}

let rec merge xs ys =
  match (xs, ys) with
  | [], zs | zs, [] -> zs
  | x :: xs, y :: ys when x = y -> x :: merge xs ys
  | x :: xs, y :: ys when x < y -> x :: y :: merge xs ys
  | x :: xs, y :: ys -> y :: x :: merge xs ys

let union
    {assumptions= a1; identifiers= i1; constraints= c1}
    {assumptions= a2; identifiers= i2; constraints= c2} =
  {assumptions= merge a1 a2; identifiers= merge i1 i2; constraints= merge c1 c2}

let add_fvar x_name x_rep x_kind = on_identifiers (List.cons (x_name, K_FVar (x_rep, x_kind)))

let add_constr constr = on_constraints (List.cons constr)

let add_assumption item = union (singleton item)

let map_assumptions f = on_assumptions (List.map f)

let lookup_assumption test {assumptions; _} = List.find_opt test assumptions

let remove_assumptions test = on_assumptions (List.filter (not % test))

let pp_print_env pp_print_assupmtion fmt {assumptions; identifiers; constraints} =
  let pp_sep fmt () = pp_print_string fmt "; " in
  pp_print_identifier_env fmt identifiers ;
  pp_print_bracketed (pp_print_list ~pp_sep pp_print_constr) fmt constraints ;
  pp_print_bracketed (pp_print_list ~pp_sep pp_print_assupmtion) fmt assumptions
