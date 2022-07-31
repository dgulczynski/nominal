open Nominal.Parser
open Nominal.ParserCommon
open Nominal.Common

let env =
  [ ("a", PI_Atom)
  ; ("b", PI_Atom)
  ; ("c", PI_Atom)
  ; ("d", PI_Atom)
  ; ("x", PI_Var)
  ; ("y", PI_Var)
  ; ("z", PI_Var)
  ; ("w", PI_Var) ]

let iter () =
  try
    let res = run_judgement env $ read_line () in
    Printf.printf "%s\n" (if res then "✅" else "❌")
  with
  | ParserException e -> Printf.printf "Parsing error: %s\n" e
  | End_of_file       -> exit 0
  | e                 -> raise e

let rec loop iter () = iter () ; loop iter ()

let _ =
  Printf.printf
    "Input judgement of form << a_1; ...; a_n |- goal >> to run solver on goal\n\
    \   with assumptions  a_1, ... a_n\n"

let _ = loop iter ()
