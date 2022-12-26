open Nominal.Common
open Nominal.Parser
open Nominal.ProofEnv
open Nominal.ProofException
open Nominal.Prover
open Nominal.ProverGoal
open Nominal.Tactics
open Nominal.Types

let test_proof theorem proof =
  Printf.printf "Checking proof of `%s` ... " $ string_of_goal theorem ;
  let _ =
    try theorem |> proof |> qed
    with ProofException e ->
      Printf.printf "❌ \n%s\n" e ;
      assert false
  in
  Printf.printf "✅\n"

let th1 =
  let env1 = fvars_env [("p", K_Prop); ("q", K_Prop)] in
  (env env1 [] [], parse_formula_in_env env1 "(p => q) => p => q")

let proof1 th1 = proof' th1 |> intro "HPQ" |> intro "HP" |> apply_assm "HPQ" |> apply_assm "HP"

let th2 =
  let env2 = fvars_env [("p", K_Prop); ("q", K_Prop); ("r", K_Prop)] in
  (env env2 [] [], parse_formula_in_env env2 "(p => q => r) => (p => q) => p => r")

let proof2 th2 =
  proof' th2 |> intro "HPQR" |> intro "HPQ" |> intro "HP" |> apply_assm "HPQR" |> assumption
  |> apply_assm "HPQ" |> apply_assm "HP"

let th3 =
  let env3 = fvars_env [("p", K_Prop)] in
  (env env3 [] [], parse_formula_in_env env3 "(((p => ⊥) => p) => p) => ((p => ⊥) => ⊥) => p")

let proof3 th3 =
  proof' th3 |> intro "H1" |> intro "H2" |> apply_assm "H1" |> intro "H3" |> ex_falso
  |> apply_assm "H2" |> apply_assm "H3"

let th4 =
  let env4 = fvars_env [("p", K_Prop)] in
  (env env4 [] [], parse_formula_in_env env4 "(((p => ⊥) => ⊥) => p) => ((p => ⊥) => p) => p")

let proof4 th4 =
  proof' th4
  |> intros ["H1"; "H2"]
  |> apply_assm "H1" |> intro "H3"
  |> apply_parse "(p => ⊥) => p => ⊥" %> trivial
  |> assumption |> apply_assm "H2" |> assumption

let th5 =
  let env5 = atoms_env ["a"; "b"; "c"] in
  (env env5 [] [], parse_formula_in_env env5 "[a = b] => [c =/= b] => [a # c]")

let proof5 th5 = proof' th5 |> repeat intro_constr |> by_solver

let th6 =
  let env6 = atoms_env ["a"; "b"; "c"] in
  (env env6 [] [], parse_formula_in_env env6 "([a = b] => (a # c)) => [a = b] => (c =/= b)")

let proof6 th6 =
  proof' th6 |> intro "H" |> intro_constr
  |> add_constr_parse "a # c" %> by_solver
  |> apply_assm "H" %> by_solver

let _ = test_proof th1 proof1

let _ = test_proof th2 proof2

let _ = test_proof th3 proof3

let _ = test_proof th4 proof4

let _ = test_proof th5 proof5

let _ = test_proof th6 proof6

let _ = print_newline ()
