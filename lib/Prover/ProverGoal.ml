open Format
open ProofEnv
open ProofPrinting
open Printing
open Types

type goal_env = (string * formula) env

type goal = goal_env * formula

let to_goal_env env =
  let name i h = (Printf.sprintf "H%d" i, h) in
  to_list env |> List.mapi name |> from_list

let to_env env = map snd env

let to_judgement (env, f) = (to_env env, f)

let to_goal (env, f) = (to_goal_env env, f)

let pp_print_assm fmt (name, f) =
  pp_print_string fmt name ; pp_print_string fmt ": " ; pp_print_formula fmt f

let pp_print_goal fmt goal =
  let pp_print_env = pp_print_env pp_print_assm in
  pp_print_judgement' pp_print_env fmt goal

let string_of_goal = printer_to_string pp_print_goal
