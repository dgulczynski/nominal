open Common
open Format
open ProofEnv
open ProofPrinting
open Printing
open Types

type goal_env = (string * formula) ProofEnv.env

type goal = goal_env * formula

let to_env env = ProofEnv.map_assumptions snd env

let to_judgement (env, f) = (to_env env, f)

let pp_print_assm env fmt (name, f) =
  pp_print_string fmt name ; pp_print_string fmt ": " ; pp_print_formula env fmt f

let pp_print_goal fmt goal =
  let pp_print_env = ProofEnv.pp_print_env (pp_print_assm % identifiers $ fst goal) in
  pp_print_judgement' pp_print_env fmt goal

let string_of_goal = printer_to_string pp_print_goal
