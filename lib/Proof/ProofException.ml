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

let not_a_constr_and = not_what_expected "a formula guarded by a constraint" % string_of_formula

let not_a_constraint = not_what_expected "a constraint" % string_of_formula

let not_a_forall_atom = not_what_expected "an universal quantification over atoms" % string_of_formula

let not_a_forall_term = not_what_expected "an universal quantification over terms" % string_of_formula

let not_an_exists = not_what_expected "an existential quantification" % string_of_formula

let not_a_disjunction = not_what_expected "a disjunction" % string_of_formula

let not_what_with what with_what = not_what_expected (Printf.sprintf "a %s with %s" what with_what)

let not_a_conjunction_with conjunct =
  not_what_with "a conjunction" (string_of_formula conjunct) % string_of_formula

let not_a_disjunction_with disjunct =
  not_what_with "a disjunction" (string_of_formula disjunct) % string_of_formula

let premise_mismatch hypothesis premise =
  not_what_expected ("implication with premise " ^ string_of_formula premise) (string_of_formula hypothesis)

let conclusion_mismatch hypothesis conclusion =
  not_what_expected
    ("implication with conclusion " ^ string_of_formula conclusion)
    (string_of_formula hypothesis)

let formula_mismatch env expected actual =
  let string_of_formula = string_of_formula_in_env env in
  not_what_expected (string_of_formula expected) (string_of_formula actual)

let formula_kind_mismatch f f_kind expected_kind =
  let expcted_kind = Printf.sprintf "formula with kind %s" (string_of_kind expected_kind) in
  let actual_kind = Option.fold ~none:"None" ~some:string_of_kind f_kind in
  let actual = Printf.sprintf "%s of kind %s" (string_of_formula f) actual_kind in
  not_what_expected expcted_kind actual

let hole_in_proof = ProofException "Proof cannot have holes"

let solver_failure constraints goal =
  let constrs' = string_of_list string_of_constr constraints in
  let goal' = string_of_formula goal in
  let exn = Printf.sprintf "Solver cannot solve %s |- %s" constrs' goal' in
  ProofException exn

let cannot_generalize name env f =
  let f = string_of_formula_in_env env f in
  let exn = Printf.sprintf "Cannot generalize %s as it is bound in %s" name f in
  ProofException exn

let cannot_destruct f =
  let exn = Printf.sprintf "Cannot destruct %s" (string_of_formula f) in
  ProofException exn

let cannot_infer_kind f_source =
  let exn = Printf.sprintf "Cannot infer kind of formula `%s`" f_source in
  ProofException exn

let unknown_case case f =
  let exn = Printf.sprintf "There is no case `%s` in `%s`" case (string_of_formula f) in
  ProofException exn

let cannot_specialize f =
  let exn =
    Printf.sprintf "Only implications and foralls can be specialized, not `%s`" (string_of_formula f)
  in
  ProofException exn

let name_taken x =
  let exn = Printf.sprintf "Name `%s` is already taken" x in
  ProofException exn
