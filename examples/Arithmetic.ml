open Nominal
open Common
open Parser
open ProofEnv
open Prover
open Tactics
open Printing

let arith_symbols = funcs_env ["0"; "S"]

let is_num =
  unwords
    [ "fix IsNum(n) : * =                             "
    ; "  zero: n = 0                                  "
    ; "  ∨                                            "
    ; "  succ: (exists m :term. [n = S m] ∧ IsNum m)" ]

let plus_eq =
  unwords
    [ "fix PlusEq(n) : forall m k : term. * = fun m : term -> fun k : term ->  "
    ; "  zero: ([n = 0] ∧ [m = k])                                             "
    ; "  ∨                                                                     "
    ; "  succ: (exists n' k' :term. [n = S n'] ∧ [k = S k'] ∧ PlusEq n' m k')" ]

let arith_env = parse_mapping arith_symbols [] [] snd [("IsNum", is_num); ("PlusEq", plus_eq)]

let arith_thm f = (arith_env, parse_formula_in_env (all_identifiers arith_env) f)

let plus_1_n_thm = arith_thm "forall n : term. PlusEq {S 0} {n} {S n}"

let plus_1_n =
  proof' plus_1_n_thm |> intro
  |> case "succ" %> exists "0" %> exists "n" %> repeat by_solver %> compute
  |> case "zero" %> repeat by_solver
  |> qed

let plus_n_1_thm = arith_thm "forall n:term. (IsNum n) => (PlusEq {n} {S 0} {S n})"

let plus_n_1 =
  proof' plus_n_1_thm |> by_induction "n0" "H0"
  |> intros ["Hn"] %> destruct_assm "Hn" (* case analysis on (IsNum n) *)
  |> intros ["Hn"] %> compute (* n = 0 *)
  |> case "zero" %> repeat by_solver
  |> intros ["Hm"] %> destruct_assm "Hm" %> destruct_assm "Hm" %> compute (* n = S m *)
  |> case "succ" %> exists "m" %> exists "n" %> repeat by_solver
  |> apply_assm_specialized "H0" ["m"] %> by_solver %> assumption
  |> qed

let plus_n_Sm_thm = arith_thm "forall x y z :term. (PlusEq {S x} y z) => (PlusEq x {S y} z)"

let plus_n_Sm =
  proof' plus_n_Sm_thm
  |> by_induction "x'" "IH" %> intro %> intro
  |> intros ["H"] %> destruct_assm "H" (* case analysis on PlusEq {S x} y z *)
  |> intros' ["contra"; "_"] %> ex_falso %> by_solver (* S x = 0 *)
  |> intros' ["H"; "x'"; "z'"; "_"; "_"] (* S x = S x', z = S z', PlusEq (S x') y (S z') *)
  |> destruct_assm "H" (* case analysis on PlusEq (S x') y (S z') *)
  |> intros' ["H0"; "_"] %> case "zero" %> by_solver %> by_solver (* x' = 0, y = z' *)
  |> intros' ["HS"; "x''"; "z''"; "_"; "_"] (* x' = S x'', z' = S z'', PlusEq x'' y z'' *)
     %> case "succ" %> exists "x''" %> exists "z'" %> by_solver %> by_solver
     %> apply_assm_specialized "IH" ["x''"; "y"; "z'"] (* (PlusEq {S x''} y z') => (PlusEq x'' {S y} z') *)
     %> by_solver %> case "succ" %> exists "x''" %> exists "z''" %> by_solver %> by_solver %> apply_assm "HS"
  |> qed

let plus_Sn_m_thm = arith_thm "forall x y z :term. (PlusEq x {S y} z) => (PlusEq {S x} y z)"

let plus_Sn_m =
  proof' plus_Sn_m_thm
  |> by_induction "x'" "IH" %> intro %> intro
  |> intros ["H"] %> destruct_assm "H" (* case analysis on PlusEq x {S y} z *)
  |> intros' ["H0"; ""] (* x = 0 *)
     %> (case "succ" %> exists "0" %> exists "y" %> by_solver %> by_solver)
     %> (case "zero" %> by_solver %> by_solver)
  |> intros' ["HS"; "x'"; "z'"; ""; ""] (* x = S x', z = S z', PlusEq x' {S y} z' *)
     %> case "succ" %> exists "x" %> exists "z'" %> by_solver %> by_solver
     %> apply_assm_specialized "IH" ["x'"; "y"; "z'"]
     %> by_solver %> apply_assm "HS"
  |> qed

let plus_symm_thm = arith_thm "forall x y z :term. (IsNum x) => (IsNum y) => (PlusEq x y z) => (PlusEq y x z)"

let plus_symm =
  let intros20 = by_induction "x0" "Hx0" %> by_induction "y0" "Hy0" %> intro %> intros ["Hx"; "Hy"; "Heq"] in
  let case0 =
    intros' ["H0"; ""] (* x = 0 /\ y = z /\ PlusEq 0 y z => PlusEq y 0 z *)
    %> destruct_assm "Hy" (* case analysis on IsNum y *)
    %> (intros ["Hy"] %> case "zero" %> by_solver %> by_solver) (* y = 0 *)
    %> ( intros' ["Hy"; "y'"; ""] (* y = S y' /\ IsNum y' *)
       %> case "succ" %> exists "y'" %> exists "y'" %> by_solver %> by_solver
       %> apply_assm_specialized "Hy0" ["y'"; "y'"] (* (PlusEq 0 y' y') => (PlusEq y' 0 y') *)
       %> by_solver %> apply_assm "Hx" %> apply_assm "Hy" %> case "zero" %> by_solver %> by_solver )
  in
  let caseS =
    intros' ["Heq"; "x'"; "z'"; "_"; "_"] (* x = S x' /\ z = S z' /\ PlusEq x' y z' => PlusEq y x' z' *)
    %> destruct_assm "Hx" %> intros ["contra"] %> ex_falso %> by_solver (* x = 0 *)
    %> intros' ["Hx"; "x0"; "_"]
    %> subst "x0" "x'" %> subst "x" "S x'" (* x = S x'*)
    %> rename "y" "y'" (* rename y to y' to avoid capture *)
    %> apply_thm_specialized plus_n_Sm ["y'"; "x'"; "z"] (* (PlusEq {S y'} x' z') => (PlusEq y' {S x'} z') *)
    %> case "succ" %> exists "y'" %> exists "z'" %> by_solver %> by_solver
    %> apply_assm_specialized "Hx0" ["x'"; "y'"; "z'"] (* (PlusEq x' y' z') => (PlusEq y' x' z') *)
    %> by_solver %> apply_assm "Hx" %> apply_assm "Hy" %> apply_assm "Heq"
  in
  (* case analysis on PlusEq x y z*)
  proof' plus_symm_thm |> intros20 |> destruct_assm "Heq" |> case0 |> caseS |> qed
