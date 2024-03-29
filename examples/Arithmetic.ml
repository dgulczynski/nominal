open Nominal
open Prelude
open Parser
open ProofEnv
open Prover
open Tactics

let arith_symbols = symbols ["0"; "S"]

let is_num =
  unwords
    [ "fix IsNum(n) : * =                             "
    ; "  zero: n = 0                                  "
    ; "  ∨                                            "
    ; "  succ: (exists m :term. [n = S m] ∧ IsNum m)" ]

let plus_eq =
  unwords
    [ "fix PlusEq(n) : forall m k : term. * = fun m k : term ->                "
    ; "  zero: ([n = 0] ∧ [m = k])                                             "
    ; "  ∨                                                                     "
    ; "  succ: (exists n' k' :term. [n = S n'] ∧ [k = S k'] ∧ PlusEq n' m k')" ]

let arith_env = parse_mapping arith_symbols [] [] snd [("IsNum", is_num); ("PlusEq", plus_eq)]

let arith_thm f = (arith_env, parse_formula_in_env (all_identifiers arith_env) f)

let plus_1_n_thm = arith_thm "forall n : term. PlusEq {S 0} {n} {S n}"

let plus_1_n =
  proof' plus_1_n_thm
  |> intro
  |> case "succ" %> exists "0" %> exists "n" %> repeat solve %> compute
  |> case "zero" %> repeat solve
  |> qed

let plus_n_1_thm = arith_thm "forall n:term. (IsNum n) => (PlusEq {n} {S 0} {S n})"

let plus_n_1 =
  proof' plus_n_1_thm
  |> by_induction "n0" "H0"
  |> intros ["Hn"] %> destruct_assm "Hn" (* case analysis on (IsNum n) *)
  |> intros ["Hn"] %> compute (* n = 0 *)
  |> case "zero" %> repeat solve
  |> intros ["Hm"] %> destruct_assm "Hm" %> destruct_assm "Hm" %> compute (* n = S m *)
  |> case "succ" %> exists "m" %> exists "n" %> repeat solve
  |> apply_assm_spec "H0" ["m"] %> solve %> assumption
  |> qed

let plus_n_Sm_thm = arith_thm "forall x y z :term. (PlusEq {S x} y z) => (PlusEq x {S y} z)"

let plus_n_Sm =
  proof' plus_n_Sm_thm
  |> by_induction "x'" "IH" %> intros ["y"; "z"; "H"] %> destruct_assm "H" (* case analysis on PlusEq {S x} y z *)
  |> intros' ["contra"; "_"] %> discriminate (* S x = 0 *)
  |> intros' ["H"; "x'"; "z'"; "_"; "_"] (* S x = S x', z = S z', PlusEq (S x') y (S z') *)
  |> destruct_assm "H" (* case analysis on PlusEq (S x') y (S z') *)
  |> intros' ["H0"; "_"] %> case "zero" %> solve %> solve (* x' = 0, y = z' *)
  |> intros' ["HS"; "x''"; "z''"; "_"; "_"] (* x' = S x'', z' = S z'', PlusEq x'' y z'' *)
     %> case "succ"
     %> exists "x''"
     %> exists "z'"
     %> solve
     %> solve
     %> apply_assm_spec "IH" ["x''"; "y"; "z'"] (* (PlusEq {S x''} y z') => (PlusEq x'' {S y} z') *)
     %> solve
     %> case "succ"
     %> exists "x''"
     %> exists "z''"
     %> solve
     %> solve
     %> apply_assm "HS"
  |> qed

let plus_Sn_m_thm = arith_thm "forall x y z :term. (PlusEq x {S y} z) => (PlusEq {S x} y z)"

let plus_Sn_m =
  proof' plus_Sn_m_thm
  |> by_induction "x'" "IH" %> intros ["y"; "z"; "H"] %> destruct_assm "H" (* case analysis on PlusEq x {S y} z *)
  |> intros' ["H0"; ""] (* x = 0 *)
     %> (case "succ" %> exists "0" %> exists "y" %> solve %> solve)
     %> (case "zero" %> solve %> solve)
  |> intros' ["HS"; "x'"; "z'"; ""; ""] (* x = S x', z = S z', PlusEq x' {S y} z' *)
     %> case "succ"
     %> exists "x"
     %> exists "z'"
     %> solve
     %> solve
     %> apply_assm_spec "IH" ["x'"; "y"; "z'"]
     %> solve
     %> apply_assm "HS"
  |> qed

let plus_symm_thm = arith_thm "forall x y z :term. (IsNum x) => (IsNum y) => (PlusEq x y z) => (PlusEq y x z)"

let plus_symm =
  let case0 =
    intros' ["H0"; ""] (* x = 0 /\ y = z /\ PlusEq 0 y z => PlusEq y 0 z *)
    %> destruct_assm "Hy" (* case analysis on IsNum y *)
    %> (intros ["Hy"] %> case "zero" %> solve %> solve) (* y = 0 *)
    %> ( intros' ["Hy"; "y'"; ""] (* y = S y' /\ IsNum y' *)
       %> case "succ"
       %> exists "y'"
       %> exists "y'"
       %> solve
       %> solve
       %> apply_assm_spec "Hy0" ["y'"; "y'"] (* (PlusEq 0 y' y') => (PlusEq y' 0 y') *)
       %> solve
       %> apply_assm "Hx"
       %> apply_assm "Hy"
       %> case "zero"
       %> solve
       %> solve )
  in
  let caseS =
    intros' ["Heq"; "x'"; "z'"; "_"; "_"] (* x = S x' /\ z = S z' /\ PlusEq x' y z' => PlusEq y x' z' *)
    %> destruct_assm "Hx"
    %> intros ["contra"]
    %> discriminate (* x = 0 *)
    %> intros' ["Hx"; "x0"; "_"]
    %> subst "x0" "x'"
    %> subst "x" "S x'" (* x = S x'*)
    %> apply_thm_spec plus_n_Sm ["y"; "x'"; "z"] (* (PlusEq {S y} x' z') => (PlusEq y {S x'} z') *)
    %> case "succ"
    %> exists "y"
    %> exists "z'"
    %> solve
    %> solve
    %> apply_assm_spec "Hx0" ["x'"; "y"; "z'"] (* (PlusEq x' y z') => (PlusEq y x' z') *)
    %> solve
    %> apply_assm "Hx"
    %> apply_assm "Hy"
    %> apply_assm "Heq"
  in
  proof' plus_symm_thm
  |> by_induction "x0" "Hx0" %> by_induction "y0" "Hy0" %> intros ["z"; "Hx"; "Hy"; "Heq"]
  |> destruct_assm "Heq" %> case0 %> caseS (* case analysis on PlusEq x y z*)
  |> qed
