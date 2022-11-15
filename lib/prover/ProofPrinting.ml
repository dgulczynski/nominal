open Printing
open Format

let pp_sep fmt () = pp_print_string fmt "; "

let pp_print_judgement' pp_print_env fmt (env, f) =
  pp_print_env fmt env ; pp_print_string fmt " ⊢ " ; pp_print_formula fmt f

let pp_print_judgement =
  let pp_print_env = pp_print_list ~pp_sep pp_print_formula in
  pp_print_judgement' pp_print_env

let pp_print_assm fmt (name, f) =
  pp_print_string fmt name ; pp_print_string fmt ": " ; pp_print_formula fmt f

let pp_print_goal =
  let pp_print_env = pp_print_list ~pp_sep pp_print_assm in
  pp_print_judgement' pp_print_env

let string_of_goal = printer_to_string pp_print_goal

let string_of_judgement = printer_to_string pp_print_judgement