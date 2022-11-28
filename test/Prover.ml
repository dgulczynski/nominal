open Nominal.Common
open Nominal.IncProof
open Nominal.Parser
open Nominal.ProofPrinting
open Nominal.ProofEnv
open Nominal.ProofException
open Nominal.Prover
open Nominal.Tactics

let test_proof theorem proof =
  Printf.printf "Checking proof of `%s` ... " $ string_of_judgement theorem ;
  let _ =
    try theorem |> proof |> qed |> incproof_to_proof
    with ProofException e ->
      Printf.printf "❌ \n%s\n" e ;
      assert false
  in
  Printf.printf "✅\n"

let th1 = (empty, parse_formula_in_env (fvars_env ["p"; "q"]) "(p => q) => p => q")

let proof1 th1 = proof' th1 |> intro "HPQ" |> intro "HP" |> apply_assm "HPQ" |> apply_assm "HP"

let th2 =
  (empty, parse_formula_in_env (fvars_env ["p"; "q"; "r"]) "(p => q => r) => (p => q) => p => r")

let proof2 th2 =
  proof' th2 |> intro "HPQR" |> intro "HPQ" |> intro "HP" |> apply_assm "HPQR" |> apply_assm "HPQ"
  |> apply_assm "HP" |> assumption

let th3 =
  (empty, parse_formula_in_env (fvars_env ["p"]) "(((p => ⊥) => p) => p) => ((p => ⊥) => ⊥) => p")

let proof3 th3 =
  proof' th3 |> intro "H1" |> intro "H2" |> apply_assm "H1" |> intro "H3" |> ex_falso
  |> apply_assm "H2" |> apply_assm "H3"

let th4 =
  (empty, parse_formula_in_env (fvars_env ["p"]) "(((p => ⊥) => ⊥) => p) => ((p => ⊥) => p) => p")

let proof4 th4 =
  proof' th4
  |> intros ["H1"; "H2"]
  |> apply_assm "H2" |> intro "H3"
  |> apply (parse_formula_in_env (fvars_env ["p"]) "(p => ⊥) => p => ⊥")
  |> apply_assm "H1" |> apply_assm "H3" |> apply_assm "H3" |> trivial

let _ = test_proof th1 proof1

let _ = test_proof th2 proof2

let _ = test_proof th3 proof3

let _ = test_proof th4 proof4

let _ = print_newline ()
