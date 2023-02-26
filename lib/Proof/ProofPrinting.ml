open Format
open Printing
open ProofEnv

let pp_print_judgement' pp_print_env fmt (env, f) =
  pp_print_env fmt env ;
  pp_print_string fmt " ⊢ " ;
  pp_print_formula (all_identifiers env) fmt f

let pp_print_judgement =
  let pp_print_env fmt env = pp_print_env (pp_print_formula (identifiers env)) fmt env in
  pp_print_judgement' pp_print_env

let string_of_judgement = printer_to_string pp_print_judgement
