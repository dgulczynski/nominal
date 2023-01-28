open Common
open Format
open Printing
open Types
open Utils

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

let add_fvar x_name x_rep x_kind = on_identifiers $ merge [(x_name, K_FVar (x_rep, x_kind))]

let add_atom a = on_identifiers $ merge [(a, K_Atom)]

let add_var x = on_identifiers $ merge [(x, K_Var)]

let add_constr constr = on_constraints (List.cons constr)

let add_assumption ass = on_assumptions $ merge [ass]

let map_assumptions f = on_assumptions (List.map f)

let lookup_assumption test {assumptions; _} = List.find_opt test assumptions

let lookup_identifier name {identifiers; _} = List.find_opt (fun (x, _) -> x = name) identifiers

let unfilter test = List.filter (not % test)

let remove_assumptions test = on_assumptions $ unfilter test

let remove_constraints test = on_constraints $ unfilter test

let remove_identifiers test = on_identifiers $ unfilter test

let remove_identifier x = remove_identifiers $ ( = ) x % fst

let kind_checker_env {identifiers; _} =
  let add_identifier env = function
    | x_name, K_FVar (x, k) -> KindCheckerEnv.map_fvar env x_name (FV x) k
    | _                     -> env
  in
  List.fold_left add_identifier KindCheckerEnv.empty identifiers

let find_bind to_formula name {assumptions; constraints; _} =
  let bound_in_assumption = List.exists (( = ) name) % free_names_of_formula % to_formula in
  let bound_in_constr = List.exists (( = ) name) % free_names_of_constr in
  let from_constr c = F_Constr c in
  match List.find_opt bound_in_assumption assumptions with
  | Some f -> Some (to_formula f)
  | None   -> from_constr <$> List.find_opt bound_in_constr constraints

let pp_print_env pp_print_assupmtion fmt {assumptions; identifiers; constraints} =
  let pp_sep fmt () = pp_print_string fmt "; " in
  pp_print_identifier_env fmt identifiers ;
  pp_print_bracketed (pp_print_list ~pp_sep pp_print_constr) fmt constraints ;
  pp_print_bracketed (pp_print_list ~pp_sep pp_print_assupmtion) fmt assumptions
