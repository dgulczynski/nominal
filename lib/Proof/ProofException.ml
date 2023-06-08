open Prelude
open PrettyPrintingFormula
open PrettyPrintingCore

exception ProofException of string

let proof_exception exn = ProofException exn

let proof_exception_from_printer printer env = proof_exception $ printer_to_string (const printer) env ()

let proof_finished = proof_exception "Proof finished"

let unknown_hypothesis h_name =
  let exn = Printf.sprintf "Hypothesis \"%s\" not in environment" h_name in
  proof_exception exn

let hole_in_proof = proof_exception "Proof cannot have holes"

let name_taken x =
  let exn = Printf.sprintf "Name `%s` is already taken" x in
  proof_exception exn

let cannot_infer_kind f_source =
  let exn = Printf.sprintf "Cannot infer kind of formula `%s`" f_source in
  ProofException exn

let pretty_sprintf fmt = str % Printf.sprintf fmt

let backticked_formula f = backticked (pretty_formula f)

let hypothesis_goal_mismatch env h_name h_formula goal =
  let exn =
    unwords
      [ pretty_sprintf "Cannot apply hypothesis %s:" h_name
      ; backticked_formula h_formula
      ; str "on goal"
      ; backticked_formula goal ]
  in
  proof_exception_from_printer exn env

let not_what_expected expected instead env =
  let exn = sequence [str "Expected"; expected; str "but got"; instead; str "instead."] in
  proof_exception_from_printer exn env

let not_an_implication = not_what_expected (str "an implication") % backticked_formula

let not_a_constr_implication = not_what_expected (str "a constraint implication") % backticked_formula

let not_a_constr_and = not_what_expected (str "a formula guarded by a constraint") % backticked_formula

let not_a_constraint = not_what_expected (str "a constraint") % backticked_formula

let not_a_forall_atom = not_what_expected (str "an universal quantification over atoms") % backticked_formula

let not_a_forall_term = not_what_expected (str "an universal quantification over terms") % backticked_formula

let not_an_exists = not_what_expected (str "an existential quantification") % backticked_formula

let not_a_disjunction = not_what_expected (str "a disjunction") % backticked_formula

let not_a_conjunction_with conjunct =
  not_what_expected (with_prefix "a conjunction with " $ backticked_formula conjunct) % backticked_formula

let not_a_disjunction_with disjunct =
  not_what_expected (with_prefix "a disjunction with " $ backticked_formula disjunct) % backticked_formula

let premise_mismatch hypothesis premise =
  not_what_expected
    (with_prefix "implication with premise " $ backticked_formula premise)
    (backticked_formula hypothesis)

let conclusion_mismatch hypothesis conclusion =
  not_what_expected
    (with_prefix "implication with conclusion " $ backticked_formula conclusion)
    (backticked_formula hypothesis)

let formula_mismatch expected actual = not_what_expected (backticked_formula expected) (backticked_formula actual)

let formula_kind_mismatch f f_kind expected_kind =
  let expected_kind = with_prefix "formula with kind " $ pretty_kind expected_kind in
  let none = str "None" in
  let actual_kind = Option.fold ~none ~some:pretty_kind f_kind in
  not_what_expected expected_kind (sequence [backticked_formula f; str "of kind"; actual_kind])

let solver_failure constraints goal =
  let exn = with_prefix "Solver cannot solve" $ pretty_solve constraints goal in
  proof_exception_from_printer exn

let cannot_generalize name f =
  let exn = sequence [pretty_sprintf "Cannot generalize %s as it is bound in " name; pretty_formula f] in
  proof_exception_from_printer exn

let cannot_destruct f =
  let exn = sequence [str "Cannot destruct"; pretty_formula f] in
  proof_exception_from_printer exn

let unknown_case case f =
  let exn = sequence [pretty_sprintf "There is no case '%s' in" case; pretty_formula f] in
  proof_exception_from_printer exn

let cannot_specialize f =
  let exn = sequence [str "Only implications and foralls can be specialized, not"; pretty_formula f] in
  proof_exception_from_printer exn
