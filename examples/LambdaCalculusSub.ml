open Nominal.Common
open Nominal.Proof
open Nominal.Prover
open Nominal.Tactics
open Nominal.Printing
open LambdaCalculusCore
open LambdaCalculusEnv

let sub_lemma_thm =
  lambda_thm
  $ unwords
      [ "forall e env t :term.            "
      ; "forall a : atom. forall ta :term."
      ; "forall v e' :term.               "
      ; "  (Typing v env ta) =>           "
      ; "  (Typing e {cons a ta env} t) =>"
      ; "  (Sub e a v e') =>              "
      ; "  (Typing e' env t)" ]

let sub_swap_lemma_thm =
  lambda_thm
  $ unwords
      [ "forall e : term."
      ; "forall a : atom. forall v e' :term."
      ; "forall b c : atom.          "
      ; "[b # a v] =>                "
      ; "[c # a v] =>                "
      ; "(Sub e a v e') =>           "
      ; "(Sub {[b c]e} a v {[b c]e'})" ]

let sub_swap_lemma =
  proof' sub_swap_lemma_thm
  |> by_induction "e0" "IH" %> repeat intro %> destr_intro
  |> intros' ["Ha"; ""] %> case "var_same" %> repeat by_solver
  |> intros' ["Hd"; "d"; ""; ""; ""] %> case "var_diff" %> exists "[b c]d" %> repeat by_solver
  |> intros' ["Hlam"; "d"; "e_d"; "e_d'"; ""; ""; ""; ""]
     %> case "lam"
     %> exists' ["[b c]d"; "[b c]e_d"; "[b c]e_d'"]
     %> repeat by_solver
     %> apply_assm_specialized "IH" ["e_d"; "a"; "v"; "e_d'"; "b"; "c"]
     %> repeat by_solver %> apply_assm "Hlam"
  |> intros' ["Happ"; "e1"; "e2"; "e1'"; "e2'"; ""; ""; ""]
     %> case "app"
     %> exists' ["[b c]e1"; "[b c]e2"; "[b c]e1'"; "[b c]e2'"]
     %> repeat by_solver %> destruct_goal
  |> apply_assm_specialized "IH" ["e1"; "a"; "v"; "e1'"; "b"; "c"] %> repeat by_solver %> apply_assm "Happ_1"
  |> apply_assm_specialized "IH" ["e2"; "a"; "v"; "e2'"; "b"; "c"] %> repeat by_solver %> apply_assm "Happ_2"
  |> qed

let sub_lemma =
  let contra_sub_var = intros' ["contra"; "_b"; ""; ""; ""] %> discriminate in
  let contra_var = intros' ["contra"; "_"; ""] %> discriminate in
  let contra_sub_lam = intros' ["contra"; "_"; "e_"; "e_'"; ""] %> discriminate in
  let contra_sub_app = intros' ["contra"; "e1"; "e2"; "e1'"; "e2'"; ""; ""] %> discriminate in
  proof' sub_lemma_thm
  |> by_induction "e0" "IH" %> repeat intro
  |> intros ["Hv"; "He"; "Hsub"] %> destruct_assm "He"
  |> intros' ["Hb"; "b"; ""; ""]
     %> intros' ["Hab"; "env'"]
     %> destruct_assm "Hsub"
     %> intros' ["Hev"; ""; ""]
     %> subst "v" "e'" %> apply_assm "Hv" %> contra_sub_var %> contra_sub_lam %> contra_sub_app
  |> intros' ["Hc"; "c"; "tc"; "env'"; ""; ""]
     %> destruct_assm "Hsub" %> contra_var
     %> intros' ["Hd"; "d"; ""; ""]
     %> case "var" %> exists "b" %> by_solver %> subst "env'" "env" %> assumption %> contra_sub_lam
     %> contra_sub_app
  |> intros' ["Hlam"; "b"; "e_b"; "t1"; "t2"; ""; ""; ""]
     %> destruct_assm "Hsub" %> contra_var %> contra_sub_var
     %> intros' ["Hsub"; "c"; "e_c"; "e_c'"; ""; ""; ""; ""]
     %> case "lam"
  |> get_fresh_atom "d" "a b e_b c e_c e_c' v env t1 t2 ta"
     %> exists' ["d"; "[d c]e_c'"; "t1"; "t2"]
     %> by_solver %> by_solver %> destruct_goal %> assumption
     %> apply_assm_specialized "IH" ["[d c]e_c"; "cons d t1 env"; "t2"; "a"; "ta"; "v"; "[d c]e_c'"]
     %> by_solver
     %> apply_thm_specialized cons_fresh_typing ["v"; "env"; "ta"; "d"; "t1"]
     %> by_solver %> apply_assm "Hv"
  |> apply_thm_specialized typing_env_shuffle ["[d c] e_c"; "env"; "t2"; "d"; "t1"; "a"; "ta"] %> by_solver
  |> apply_thm_specialized swap_lambda_typing ["e_b"; "cons a ta env"; "t2"; "b"; "d"; "t1"]
     %> by_solver %> apply_assm "Hlam_2"
  |> apply_thm_specialized sub_swap_lemma ["e_c"; "a"; "v"; "e_c'"; "d"; "c"]
     %> by_solver %> by_solver %> apply_assm "Hsub" %> contra_sub_app
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> destruct_assm "Hsub" %> contra_var %> contra_sub_var %> contra_sub_lam
     %> intros' ["Hsub"; "_e1"; "_e2"; "e1'"; "e2'"; ""; ""; ""]
     %> case "app"
     %> exists' ["e1'"; "e2'"; "t2"]
     %> by_solver %> destruct_goal
  |> apply_assm_specialized "IH" ["e1"; "env"; "arrow t2 t"; "a"; "ta"; "v"; "e1'"]
     %> by_solver %> apply_assm "Hv" %> apply_assm "Happ_1" %> apply_assm "Hsub_1"
  |> apply_assm_specialized "IH" ["e2"; "env"; "t2"; "a"; "ta"; "v"; "e2'"]
     %> by_solver %> apply_assm "Hv" %> apply_assm "Happ_2" %> apply_assm "Hsub_2"
  |> qed

let sub_swap_lemma_thm =
  lambda_thm
  $ unwords
      [ "forall e :term.         "
      ; "forall a :atom. forall v e' :term."
      ; "forall b :atom.         "
      ; "  [b # e v] =>          "
      ; "  (Sub e a v e') =>     "
      ; "  (Sub {[a b] e} b v e')" ]

let sub_swap_lemma =
  proof' sub_swap_lemma_thm
  |> by_induction "e0" "IH" %> repeat intro %> compare_atoms "a" "b"
  |> destr_intro %> trivial |> destr_intro %> destr_intro
  |> intros' ["Ha"; ""] %> case "var_same" %> repeat by_solver
  |> intros' ["Hc"; "c"; ""; ""] %> case "var_diff" %> exists "c" %> repeat by_solver
  |> intros' ["Hlam"; "c"; "e_c"; "e_c'"; ""; ""; ""; ""]
     %> get_fresh_atom "d" "a b c e v e_c e_c'"
     %> case "lam"
     %> exists' ["d"; "[a b][d c]e_c"; "[d c]e_c'"]
     %> repeat by_solver
     %> apply_thm_specialized sub_swap_lemma ["[a b]e_c"; "b"; "v"; "e_c'"; "d"; "c"]
     %> by_solver %> by_solver
     %> apply_assm_specialized "IH" ["e_c"; "a"; "v"; "e_c'"; "b"]
     %> by_solver %> by_solver %> apply_assm "Hlam"
  |> intros' ["Happ"; "e1"; "e2"; "e1'"; "e2'"; ""; ""; ""]
     %> case "app"
     %> exists' ["[a b]e1"; "[a b]e2"; "e1'"; "e2'"]
     %> repeat by_solver %> destruct_goal
     %> apply_assm_specialized "IH" ["e1"; "a"; "v"; "e1'"; "b"]
     %> repeat by_solver %> apply_assm "Happ_1"
     %> apply_assm_specialized "IH" ["e2"; "a"; "v"; "e2'"; "b"]
     %> repeat by_solver %> apply_assm "Happ_2"
  |> qed

let swap_lemma_thm = lambda_thm "forall e : term. forall a' b' : atom. (Term e) => (Term {[a' b']e})"

let swap_lemma =
  swap_lemma_thm |> proof' |> by_induction "e0" "IH" |> intro |> intro
  |> add_assumption_thm "Hcmp" Axiom.compare_atoms
  |> intros' ["Hterm"] |> destruct_assm "Hterm"
  |> intros' ["Hc"; "c"]
  |> specialize_assm "Hcmp" "Hca" ["c"; "a'"]
  |> specialize_assm "Hcmp" "Hcb" ["c"; "b'"]
  |> destruct_assm "Hcb" |> intros ["Hsame"] |> case "var" |> exists "a'" |> by_solver |> intros ["Hdiff"]
  |> destruct_assm "Hca" |> intros ["Hsame"]
  |> case "var" %> exists "b'"
  |> by_solver |> intros ["Hdiff'"]
  |> case "var" %> exists "c"
  |> by_solver
  |> intros' ["Hlam"; "c"; "e_c"; ""]
  |> specialize_assm "Hcmp" "Hca" ["c"; "a'"]
  |> specialize_assm "Hcmp" "Hcb" ["c"; "b'"]
  |> case "lam"
  |> exists "[a' b']c" %> exists "[a' b']e_c" %> by_solver
  |> apply_assm_specialized "IH" ["e_c"; "a'"; "b'"] %> by_solver %> apply_assm "Hlam"
  |> intros' ["Happ"; "e1"; "e2"; ""; ""]
  |> case "app" %> exists "[a' b']e1" %> exists "[a' b']e2"
  |> by_solver |> destruct_goal
  |> apply_assm_specialized "IH" ["e1"; "a'"; "b'"] %> by_solver %> apply_assm "Happ_1"
  |> apply_assm_specialized "IH" ["e2"; "a'"; "b'"] %> by_solver %> apply_assm "Happ_2"
  |> qed

let subst_exists_thm =
  lambda_thm
  $ unwords
      [ "forall a  :atom."
      ; "forall v  :term. (Value v) =>"
      ; "forall e  :term. (Term e) => "
      ; "exists e' :term. (Sub e a v e')" ]

let subst_exists =
  proof' subst_exists_thm |> intro |> intro |> intros ["Hv"] |> by_induction "e0" "IH"
  |> intros' ["He"; ""]
  |> intros' ["Hb"; "b"]
  |> add_assumption_thm "Hcmp" Axiom.compare_atoms
  |> specialize_assm "Hcmp" "Hab" ["a"; "b"]
  |> destruct_assm "Hab" |> intros ["Hsame"] |> exists "v" |> case "var_same" |> repeat by_solver
  |> intros ["Hdiff"] |> exists "b" |> case "var_diff" |> exists "b" |> repeat by_solver
  |> intros' ["Hlam"; "b"; "e_b"; ""]
  |> add_assumption_thm "Hfresh" Axiom.exists_fresh
  |> specialize_assm "Hfresh" "Hc" ["a v e_b"]
  |> destruct_assm' "Hc" ["c"]
  |> add_assumption_parse "He_c" "exists e_c:term. Sub {[b c]e_b} a v e_c"
  |> destruct_assm "He_c" |> exists "lam (c.e_c)" |> case "lam" |> exists "c" |> exists "[c b]e_b"
  |> exists "e_c" |> by_solver |> by_solver |> by_solver |> by_solver |> apply_assm "He_c"
  |> apply_assm_specialized "IH" ["[b c]e_b"]
  |> by_solver
  |> apply_thm_specialized swap_lemma ["e_b"; "b"; "c"]
  |> apply_assm "Hlam"
  |> intros' ["Happ"; "e1"; "e2"; ""; ""]
  |> add_assumption_parse "He1" "exists e1':term. Sub e1 a v e1'" %> destruct_assm "He1"
  |> add_assumption_parse "He2" "exists e2':term. Sub e2 a v e2'" %> destruct_assm "He2"
  |> exists "app e1' e2'" |> case "app" |> exists "e1" |> exists "e2" |> exists "e1'" |> exists "e2'"
  |> by_solver %> by_solver
  |> destruct_goal %> apply_assm "He1" %> apply_assm "He2"
  |> apply_assm_specialized "IH" ["e2"] %> by_solver %> apply_assm "Happ_2"
  |> apply_assm_specialized "IH" ["e1"] %> by_solver %> apply_assm "Happ_1"
  |> qed
