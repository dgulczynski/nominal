open Prelude
open PrettyPrintingCore
open PrettyPrintingConstr
open PrettyPrintingFormula
open ProofEnv

let pretty_judgement' pretty_assumption (env, f) =
  with_binders (all_identifiers env)
  $ unlines
      [ pretty_ocaml_list (List.map pretty_constr $ constraints env)
      ; pretty_ocaml_list (List.map pretty_assumption $ assumptions env)
      ; with_prefix "⊢ " (pretty_formula f) ]

let pretty_judgement = pretty_judgement' pretty_formula

let pretty_goal = pretty_judgement' (fun (h_name, h) -> pretty_typed (str h_name) (pretty_formula h))
