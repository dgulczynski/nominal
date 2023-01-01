open Common
open Printing

exception ProofException of string

let proof_finished = ProofException "Proof finished"

let unknown_hypothesis h_name =
  let exn = Printf.sprintf "Hypothesis \"%s\" not in environment" h_name in
  ProofException exn

let hypothesis_goal_mismatch h_name h_formula goal =
  let h_formula' = string_of_formula h_formula in
  let goal' = string_of_formula goal in
  let exn = Printf.sprintf "Cannot apply hypothesis %s`%s` on goal `%s`" h_name h_formula' goal' in
  ProofException exn

let not_what_expected expected instead =
  let exn = Printf.sprintf "Expected `%s`, but got `%s` instead" expected instead in
  ProofException exn

let not_an_implication = not_what_expected "an implication" % string_of_formula

let not_a_constr_implication = not_what_expected "a constraint implication" % string_of_formula

let not_a_constraint = not_what_expected "a constraint" % string_of_formula

let premise_mismatch hypothesis premise =
  not_what_expected
    ("implication with premise " ^ string_of_formula premise)
    (string_of_formula hypothesis)

let formula_mismatch expected actual =
  not_what_expected (string_of_formula expected) (string_of_formula actual)

let formula_kind_mismatch f f_kind expected_kind =
  let expcted_kind = Printf.sprintf "formula with kind %s" (string_of_kind expected_kind) in
  let actual_kind = Option.fold ~none:"None" ~some:string_of_kind f_kind in
  let actual = Printf.sprintf "%s of kind %s" (string_of_formula f) actual_kind in
  not_what_expected expcted_kind actual

let hole_in_proof = ProofException "Proof cannot have holes"

let solver_failure constraints constr =
  let constrs' = string_of_list string_of_constr constraints in
  let constr' = string_of_constr constr in
  let exn = Printf.sprintf "Solver cannot solve %s |- %s" constrs' constr' in
  ProofException exn

let cannot_generalize name =
  let exn = Printf.sprintf "Cannot generalize %s as it is bound in environment" name in
  ProofException exn