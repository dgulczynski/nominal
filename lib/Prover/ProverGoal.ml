open Prelude
open ProofEnv
open PrettyPrintingCore
open PrettyPrinting
open Types

type goal_env = (string * formula) ProofEnv.env

type goal = goal_env * formula

let to_env env = ProofEnv.env (identifiers env) (constraints env) (List.map snd $ assumptions env) (mapping env) id

let to_judgement (env, f) = (to_env env, f)

let string_of_goal (env, f) = printer_to_string pretty_goal (all_identifiers env) (env, f)
