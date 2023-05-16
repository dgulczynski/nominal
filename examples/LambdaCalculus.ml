open Nominal.Common
open Nominal.Prover
open Nominal.Tactics
open LambdaCalculusCore

let progress_thm = lambda_thm "forall e t :term. (Typing e nil t) => (Progressive e)"

let progress =
  proof' progress_thm
  |> by_induction "e0" "IH" %> intro %> destr_intro
  |> intros' ["Ha"; "a"; ""] (* e is a var in empty env - contradiction *)
     %> ex_falso
     %> apply_thm_specialized LambdaCalculusEnv.empty_contradiction ["a"; "t"]
     %> assumption
  |> intros' ["Hlam"; "a"; "e_a"; "t1"; "t2"; ""; ""; ""] (* e is a lambda - value *)
     %> case "value" %> case "lam"
     %> exists' ["a"; "e_a"]
     %> by_solver
     %> apply_thm_specialized LambdaCalculusUtils.typing_terms ["e_a"; "cons a t1 nil"; "t2"]
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""] (* e is an application - steps *)
  |> add_assumption_parse "He1" "Progressive e1"
  |> add_assumption_parse "He2" "Progressive e2"
  |> destruct_assm "He1" %> intros ["Hv1"] %> destruct_assm "He2"
     %> intros ["Hv2"] (* Value e1, Value e2 *)
     %> ( add_assumption_thm_specialized "He1lam" LambdaCalculusUtils.canonical_form' ["e1"; "t2"; "t"]
        %> apply_in_assm "He1lam" "Hv1" %> apply_in_assm "He1lam" "Happ_1"
        %> destruct_assm' "He1lam" ["a"; "e_a"; ""] (* He1lam: [e1 = lam (a.e_a)] ∧ (Term e_a) *) )
     %> ( add_assumption_thm_specialized "He_a" LambdaCalculusSub.subst_exists ["a"; "e2"; "e_a"]
        %> apply_in_assm "He_a" "Hv2" %> apply_in_assm "He_a" "He1lam"
        %> destruct_assm' "He_a" ["e_a'"] (* He_a: Sub e_a a e2 e_a' *) )
     %> case "steps" %> exists "e_a'" %> case "app"
     %> exists' ["a"; "e_a"; "e2"]
     %> by_solver %> destruct_goal %> apply_assm "Hv2" %> apply_assm "He_a"
  |> intros' ["Hs2"; "e2'"] (* Value e1, Steps e2 e2' *)
     %> case "steps" %> exists "app e1 e2'" %> case "app_r"
     %> exists' ["e1"; "e2"; "e2'"]
     %> by_solver %> by_solver %> destruct_goal %> apply_assm "Hv1" %> apply_assm "Hs2"
  |> intros' ["Hs1"; "e1'"] (* Steps e1 *)
     %> case "steps" %> exists "app e1' e2" %> case "app_l"
     %> exists' ["e1"; "e1'"; "e2"]
     %> by_solver %> by_solver %> apply_assm "Hs1"
  |> apply_assm_specialized "IH" ["e2"; "t2"] %> by_solver %> apply_assm "Happ_2" (* Progressive e2 *)
  |> apply_assm_specialized "IH" ["e1"; "arrow t2 t"] %> by_solver %> apply_assm "Happ_1" (* Progressive e1 *)
  |> qed

let preservation_thm =
  lambda_thm "forall e e' env t :term. (Typing e env t) => (Steps e e') => (Typing e' env t)"

let preservation =
  let deduce_app_typing =
    destruct_assm "Htyp"
    %> (intros' ["contra"; "_"; ""] %> discriminate)
    %> (intros' ["contra"; "_"; "e_"; "t1"; "t2"; ""] %> discriminate)
    %> intros' ["Happ"; "e_1"; "e_2"; "t2"; ""; ""]
  in
  proof' preservation_thm |> by_induction "e0" "IH"
  |> intro %> intro %> intro %> intros ["Htyp"; "Hstep"]
  |> destruct_assm "Hstep"
  |> intros' ["He1"; "e1"; "e1'"; "e2"; ""; ""] (* Steps e1 e1' *)
     %> deduce_app_typing %> case "app"
     %> exists' ["e1'"; "e2"; "t2"]
     %> by_solver %> destruct_goal
     %> apply_assm_specialized "IH" ["e1"; "e1'"; "env"; "arrow t2 t"]
     %> by_solver %> apply_assm "Happ_1" %> apply_assm "He1" %> apply_assm "Happ_2"
  |> intros' ["Hv1"; "v1"; "e2"; "e2'"; ""; ""; ""] (* Value e1, Steps e2 e2' *)
     %> deduce_app_typing %> case "app"
     %> exists' ["v1"; "e2'"; "t2"]
     %> by_solver %> destruct_goal %> apply_assm "Happ_1"
     %> apply_assm_specialized "IH" ["e2"; "e2'"; "env"; "t2"]
     %> by_solver %> apply_assm "Happ_2" %> assumption
  |> intros' ["Hbeta"; "a"; "e_a"; "v"; ""; ""] (* Value e1, Value e2, e1 = a.e_a, e2 = v *)
     %> deduce_app_typing %> destruct_assm "Happ_1"
     %> (intros' ["contra"; "c"; ""] %> discriminate)
     %> intros' ["Hlam"; "b"; "e_b"; "t1b"; "t2b"; ""; ""; ""]
     %> apply_thm_specialized LambdaCalculusSub.sub_lemma ["e_a"; "env"; "t"; "a"; "t2"; "v"; "e'"]
     %> apply_assm "Happ_2" %> compare_atoms "a" "b" %> destr_intro %> apply_assm "Hlam_2" %> destr_intro
     %> apply_thm_specialized LambdaCalculusEnv.swap_lambda_typing ["e_b"; "env"; "t"; "b"; "a"; "t2"]
     %> by_solver %> apply_assm "Hlam_2" %> apply_assm "Hbeta_2"
     %> (intros' ["contra"; "_e1"; "_e2"; "_t2"; ""] %> discriminate)
  |> qed
