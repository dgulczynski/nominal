open Nominal.Prelude
open Nominal.Prover
open Nominal.Tactics
open LambdaCalculusCore

let sub_lemma_thm =
  lambda_thm
  $ unwords
      [ "forall e env t :term."
      ; "forall a : atom. forall ta :term."
      ; "forall v e' :term."
      ; " (Typing v env ta) =>"
      ; " (Typing e {cons a ta env} t) =>"
      ; " (Sub e a v e') =>"
      ; "   (Typing e' env t)" ]

let sub_lemma =
  let contra_sub_var = intros' ["contra"; "_b"; ""; ""; ""] %> discriminate in
  let contra_var = intros' ["contra"; "_"; ""] %> discriminate in
  let contra_sub_lam = intros' ["contra"; "_"; "e_"; "e_'"; ""] %> discriminate in
  let contra_sub_app = intros' ["contra"; "e1"; "e2"; "e1'"; "e2'"; ""; ""] %> discriminate in
  proof' sub_lemma_thm
  |> by_induction "e0" "IH" %> repeat intro %> intros ["Hv"; "He"; "Hsub"] %> destruct_assm "He"
  |> intros' ["Hb"; "b"; ""]
     %> destruct_assm "Hsub"
     %> ( intros' ["Heq"; ""; ""] (* e = a, e' = v *)
        %> destruct_assm "Hb"
        %> intros' ["Heq"; "env'"; ""]
        %> apply_assm "Hv"
        %> intros' ["Hdiff"; "b'"; "t'"; "env'"; ""; ""]
        %> discriminate )
     %> ( intros' ["Hdiff"; "b'"; ""; ""; ""] (* e = b, e' = b *)
        %> destruct_assm "Hb"
        %> intros' ["Heq"; "env'"; ""]
        %> discriminate
        %> intros' ["Hdiff"; "a'"; "ta'"; "env'"; ""; ""]
        %> case "var"
        %> exists "b"
        %> by_solver
        %> assumption )
     %> contra_sub_lam
     %> contra_sub_app
  |> intros' ["Hlam"; "b"; "e_b"; "t1"; "t2"; ""; ""; ""]
     %> destruct_assm "Hsub"
     %> contra_var
     %> contra_sub_var
     %> ( intros' ["Hsub"; "c"; "e_c"; "e_c'"; ""; ""; ""; ""] (* e = b.e_b, e' = c.e_c' *)
        %> case "lam"
        %> exists' ["c"; "e_c'"; "t1"; "t2"]
        %> by_solver
        %> by_solver
        %> destruct_goal
        %> assumption
        %> apply_assm_specialized "IH" ["e_c"; "cons c t1 env"; "t2"; "a"; "ta"; "v"; "e_c'"]
        %> by_solver
        %> ( apply_thm_specialized LambdaCalculusEnv.cons_fresh_typing ["v"; "env"; "ta"; "c"; "t1"]
           %> by_solver
           %> apply_assm "Hv"
           %> apply_thm_specialized LambdaCalculusEnv.typing_env_shuffle ["e_c"; "env"; "t2"; "c"; "t1"; "a"; "ta"]
           %> by_solver
           %> apply_thm_specialized LambdaCalculusEnv.swap_lambda_typing
                ["b"; "e_b"; "c"; "e_c"; "cons a ta env"; "t1"; "t2"]
           %> by_solver
           %> apply_assm "Hlam_2" )
        %> apply_assm "Hsub" )
     %> contra_sub_app
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> destruct_assm "Hsub"
     %> contra_var
     %> contra_sub_var
     %> contra_sub_lam
     %> ( intros' ["Hsub"; "_e1"; "_e2"; "e1'"; "e2'"; ""; ""; ""] (* e = e1 e2, e' = e1' e2' *)
        %> case "app"
        %> exists' ["e1'"; "e2'"; "t2"]
        %> by_solver
        %> destruct_goal
        %> ( apply_assm_specialized "IH" ["e1"; "env"; "arrow t2 t"; "a"; "ta"; "v"; "e1'"]
           %> by_solver
           %> apply_assm "Hv"
           %> apply_assm "Happ_1"
           %> apply_assm "Hsub_1" )
        %> ( apply_assm_specialized "IH" ["e2"; "env"; "t2"; "a"; "ta"; "v"; "e2'"]
           %> by_solver
           %> apply_assm "Hv"
           %> apply_assm "Happ_2"
           %> apply_assm "Hsub_2" ) )
  |> qed

let swap_term_lemma_thm = lambda_thm "forall e : term. forall a b : atom. (Term e) => (Term {[a b]e})"

let swap_term_lemma =
  proof' swap_term_lemma_thm
  |> by_induction "e0" "IH" %> repeat intro %> destr_intro
  |> intros' ["Hc"; "c"] %> case "var" %> exists "[a b]c" %> by_solver
  |> intros' ["Hlam"; "c"; "e_c"; ""]
     %> case "lam"
     %> exists' ["[a b]c"; "[a b]e_c"]
     %> by_solver
     %> apply_assm_specialized "IH" ["e_c"; "a"; "b"]
     %> by_solver
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; ""; ""]
     %> case "app"
     %> exists' ["[a b]e1"; "[a b]e2"]
     %> by_solver
     %> destruct_goal
     %> apply_assm_specialized "IH" ["e1"; "a"; "b"]
     %> by_solver
     %> assumption
     %> apply_assm_specialized "IH" ["e2"; "a"; "b"]
     %> by_solver
     %> assumption
  |> qed

let subst_exists_thm =
  lambda_thm
  $ unwords
      [ "forall a :atom."
      ; "forall v :term. (Value v) =>"
      ; "forall e :term. (Term e) =>"
      ; "exists e' :term. (Sub e a v e')" ]

let subst_exists =
  proof' subst_exists_thm
  |> intros ["a"; "v"; "Hv"] %> by_induction "e0" "IH" %> destr_intro
  |> intros' ["Hb"; "b"; ""]
     %> compare_atoms "a" "b"
     %> destr_intro
     %> exists "v"
     %> case "var_same"
     %> repeat by_solver
     %> destr_intro
     %> exists "b"
     %> case "var_diff"
     %> exists "b"
     %> repeat by_solver
  |> intros' ["Hlam"; "b"; "e_b"; ""]
     %> get_fresh_atom "c" "a v e_b"
     %> ( add_assumption_parse "He_c" "exists e_c:term. Sub {[b c]e_b} a v e_c"
        %> apply_assm_specialized "IH" ["[c b]e_b"]
        %> by_solver )
     %> destruct_assm' "He_c" ["e_c"]
     %> exists "lam (c.e_c)"
     %> case "lam"
     %> exists' ["c"; "[c b]e_b"; "e_c"]
     %> repeat by_solver
     %> assumption
     %> apply_thm_specialized swap_term_lemma ["e_b"; "c"; "b"]
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; ""; ""]
     %> (add_assumption_parse "He1" "exists e1':term. Sub e1 a v e1'" %> apply_assm_specialized "IH" ["e1"] %> by_solver)
     %> (add_assumption_parse "He2" "exists e2':term. Sub e2 a v e2'" %> apply_assm_specialized "IH" ["e2"] %> by_solver)
     %> destruct_assm "He1"
     %> destruct_assm "He2"
     %> exists "app e1' e2'"
     %> case "app"
     %> exists "e1"
     %> exists "e2"
     %> exists "e1'"
     %> exists "e2'"
     %> by_solver
     %> by_solver
     %> destruct_goal
     %> apply_assm "He1"
     %> apply_assm "He2"
     %> apply_assm "Happ_2"
     %> apply_assm "Happ_1"
  |> qed
