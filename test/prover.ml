open Nominal.Common
open Nominal.IncProof
open Nominal.Parser
open Nominal.ProofPrinting
open Nominal.Prover
open Nominal.ProverException

let test_proof theorem proof =
  Printf.printf "Checking proof of `%s` ... " $ string_of_judgement theorem ;
  let _ =
    try theorem |> proof |> qed |> iproof_to_proof
    with ProverException e ->
      Printf.printf "❌ \n%s\n" e ;
      assert false
  in
  Printf.printf "✅\n"

let th1 = ([], parse_formula_in_env (fvars_env ["p"; "q"]) "(p => q) => p => q")

let proof1 th1 = proof' th1 |> intro "HPQ" |> intro "HP" |> apply_assm "HPQ" |> apply_assm "HP"

let th2 =
  ([], parse_formula_in_env (fvars_env ["p"; "q"; "r"]) "(p => q => r) => (p => q) => p => r")

let proof2 th2 =
  proof' th2 |> intro "HPQR" |> intro "HPQ" |> intro "HP" |> apply_assm "HPQR" |> apply_assm "HPQ"
  |> apply_assm "HP" |> apply_assm "HP"

let _ = test_proof th1 proof1

let _ = test_proof th2 proof2

let _ = print_newline ()
