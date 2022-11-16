open Printing

exception ProverException of string

let finished = ProverException "Proof finished"

let unknown_hypothesis h_name =
  let exn = Printf.sprintf "Hypothesis \"%s\" not in environment" h_name in
  ProverException exn

let hypothesis_goal_mismatch h_name h_formula goal =
  let h_name' = Option.fold ~none:"" ~some:(Printf.sprintf " \"%s\"") h_name in
  let h_formula' = string_of_formula h_formula in
  let goal' = string_of_formula goal in
  let exn = Printf.sprintf "Hypothesis%s is `%s`, but goal is `%s`" h_name' h_formula' goal' in
  ProverException exn

let not_an_implication f =
  let exn = Printf.sprintf "`%s` is not an implication" (string_of_formula f) in
  ProverException exn

let conclusion_mismatch h c =
  let h' = string_of_formula h in
  let c' = string_of_formula c in
  let exn = Printf.sprintf "`%s` is not an implication with hypothesis `%s`" h' c' in
  ProverException exn

let formula_mismatch expected actual =
  let e' = string_of_formula expected in
  let a' = string_of_formula actual in
  let exn = Printf.sprintf "Expected `%s`, but got `%s` instead" e' a' in
  ProverException exn

let hole_in_proof = ProverException "Proof cannot have holes"
