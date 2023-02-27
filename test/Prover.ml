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
  (env env1 [] [] [], parse_formula_in_env env1 "(p => q) => p => q")

let proof1 th1 = proof' th1 |> intros ["HPQ"; "HP"] |> apply_assm "HPQ" |> apply_assm "HP"

let th2 =
  let env2 = fvars_env [("p", K_Prop); ("q", K_Prop); ("r", K_Prop)] in
  (env env2 [] [] [], parse_formula_in_env env2 "(p => q => r) => (p => q) => p => r")

let proof2 th2 =
  proof' th2
  |> intros ["HPQR"; "HPQ"; "HP"]
  |> apply_assm "HPQR" |> assumption |> apply_assm "HPQ" |> apply_assm "HP"

let th3 =
  let env3 = fvars_env [("p", K_Prop)] in
  (env env3 [] [] [], parse_formula_in_env env3 "(((p => ⊥) => p) => p) => ((p => ⊥) => ⊥) => p")

let proof3 th3 =
  proof' th3
  |> intros ["H1"; "H2"]
  |> apply_assm "H1" |> intros ["H3"] |> ex_falso |> apply_assm "H2" |> apply_assm "H3"

let th4 =
  let env4 = fvars_env [("p", K_Prop)] in
  (env env4 [] [] [], parse_formula_in_env env4 "(((p => ⊥) => ⊥) => p) => ((p => ⊥) => p) => p")

let proof4 th4 =
  proof' th4
  |> intros ["H1"; "H2"]
  |> apply_assm "H1" |> intros ["H3"]
  |> apply_parse "(p => ⊥) => p => ⊥" %> trivial
  |> assumption |> apply_assm "H2" |> assumption

let th5 =
  let env5 = atoms_env ["a"; "b"; "c"] in
  (env env5 [] [] [], parse_formula_in_env env5 "[a = b] => [c =/= b] => [a # c]")

let proof5 th5 = proof' th5 |> repeat intro |> by_solver

let th6 =
  let env6 = atoms_env ["a"; "b"; "c"] in
  (env env6 [] [] [], parse_formula_in_env env6 "([a = b] => (a # c)) => [a = b] => (c =/= b)")

let proof6 th6 =
  proof' th6 |> intros ["H"] |> intro
  |> add_constr_parse "a # c" %> by_solver
  |> apply_assm "H" %> by_solver

let th7 = (empty, parse_formula empty "forall a : atom. forall b : atom. [a =/= b] => [a # b]")

let proof7 th7 = proof' th7 |> repeat intro |> by_solver

let th8 =
  let env8 = atoms_env ["b"; "c"] @ vars_env ["y"] in
  ( env env8 [] [] []
  , parse_formula_in_env env8
  "(forall a : atom. forall x : term. [a = x] => [a.a = a.x]) => [c = b.[b c]y] => [c.c = c.b.[b c] y]" [@ocamlformat "disable"]
  )

let proof8 th8 = proof' th8 |> intros ["H"] |> apply_assm_specialized "H" ["c"; "b. [b c]y"]

let th9 =
  let env9 = atoms_env ["c"; "d"] in
  (env env9 [] [] [], parse_formula_in_env env9 "[c # d] => exists a:atom. exists b:atom. [a =/= b]")

let proof9 th9 = proof' th9 |> intro |> exists "d" |> exists "c" |> by_solver

let th10 =
  (empty, parse_formula empty "forall a : atom. (exists b: atom. [a =/= b]) => exists t:term. a # t")

let proof10 th10 =
  proof' th10 |> intro |> intros ["H"] |> destruct_assm "H" |> exists "b" |> by_solver

let th11 =
  ( empty
  , parse_formula empty
      "(forall a : atom. exists b: atom. [a =/= b]) => (forall a:atom. exists t:term. a # t)" )

let proof11 th11 =
  proof' th11 |> intros ["H"] |> intro
  |> add_assumption_parse "Hc" "exists c:atom. a =/= c"
  |> destruct_assm "Hc" |> exists "c" |> by_solver |> apply_assm_specialized "H" ["a"]

let th12 =
  let env12 = fvars_env [("p", K_Prop); ("q", K_Prop); ("r", K_Prop)] in
  (env env12 [] [] [], parse_formula_in_env env12 "(p ∧ q ∧ r) => (q ∧ r ∧ p)")

let proof12 = proof' %> intros ["H"] %> destruct_assm "H" %> destruct_goal %> repeat assumption

let th13 =
  let e13 = fvars_env [("p", K_Prop); ("q", K_Prop)] in
  (env e13 [] [] [], parse_formula_in_env e13 "p => p ∨ q")

let proof13 = proof' %> intros ["H"] %> left %> apply_assm "H"

let th14 =
  let e14 = fvars_env [("p", K_Prop); ("q", K_Prop); ("r", K_Prop); ("s", K_Prop)] in
  (env e14 [] [] [], parse_formula_in_env e14 "(p => s) => (q => s) => (r => s) => (p ∨ q ∨ r) => s")

let proof14 =
  proof'
  %> intros ["Hp"; "Hq"; "Hr"; "H"]
  %> destruct_assm "H" %> apply_assm "Hp" %> apply_assm "Hq" %> apply_assm "Hr"

let th15 =
  let id15 = funcs_env ["base"; "arrow"] in
  let e15 =
    parse_mapping id15 [] []
      [ ( "Type"
        , "fix Type(t):*. t = base ∨                                                            \
           (exists t1 t2:term. [t = arrow t1 t2] ∧ (Type t1) ∧ (Type t2))" ) ]
  in
  (e15, parse_formula e15 "Type {arrow base base}")

let proof15 =
  proof' %> compute %> right
  %> (exists "base" %> exists "base" %> by_solver)
  %> destruct_goal
  %> repeat (compute %> left %> by_solver)

let th16 =
  let id16 = funcs_env ["nil"; "cons"; "base"; "arrow"] @ atoms_env ["c"; "d"] in
  let e16 =
    parse_mapping id16 [] []
      [ ( "InEnv"
        , "fix InEnv(env):forall a:atom. forall t:term. *. fun a:atom -> fun t:term ->          \
           (exists env' : term. env  = cons a t env') ∨                                         \
           (exists b : atom. exists s env': term.                                               \
           [env = cons b s env'] ∧ (InEnv env' a {t}))" ) ]
  in
  (e16, parse_formula e16 "InEnv {cons c (arrow base base) (cons d base nil)} d {base}")

let proof16 =
  proof' %> compute %> right
  %> (exists "c" %> exists "arrow base base" %> exists "cons d base nil" %> by_solver)
  %> compute %> left
  %> (exists "nil" %> by_solver)

let _ = test_proof th1 proof1

let _ = test_proof th2 proof2

let _ = test_proof th3 proof3

let _ = test_proof th4 proof4

let _ = test_proof th5 proof5

let _ = test_proof th6 proof6

let _ = test_proof th7 proof7

let _ = test_proof th8 proof8

let _ = test_proof th9 proof9

let _ = test_proof th10 proof10

let _ = test_proof th11 proof11

let _ = test_proof th12 proof12

let _ = test_proof th13 proof13

let _ = test_proof th14 proof14

let _ = test_proof th15 proof15

let _ = test_proof th16 proof16

let _ = print_newline ()
