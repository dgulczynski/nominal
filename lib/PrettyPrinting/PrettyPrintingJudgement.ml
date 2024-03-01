open Prelude
open PrettyPrintingCore
open PrettyPrintingConstr
open PrettyPrintingFormula
open ProofEnv

let pretty_judgement' pretty_assm (env, f) =
  with_binders (all_identifiers env)
  $ unlines
      [ str ""
      ; pretty_ocaml_vlist (List.map pretty_constr $ constraints env)
      ; pretty_ocaml_vlist (List.map pretty_assm $ assumptions env)
      ; with_prefix "⊢ " (pretty_formula f) ]

let pretty_judgement = pretty_judgement' pretty_formula

let pretty_goal = pretty_judgement' (fun (h_name, h) -> pretty_typed (str h_name) (pretty_formula h))
