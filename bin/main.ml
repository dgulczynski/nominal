open Nominal.Parser
open Nominal.ParserCommon
open Nominal.Common

let env = atoms_env ["a"; "b"; "c"; "d"] @ vars_env ["x"; "y"; "z"; "w"]

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
    "\n\
    \ Input judgement of form `a_1; ...; a_n |- c`\n\
    \   to run solver on goal `c` with assumptions  `a_1, ... a_n`\n"

let _ = loop iter ()
