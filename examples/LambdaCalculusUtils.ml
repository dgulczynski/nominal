open Nominal.Prelude
open Nominal.Prover
open Nominal.Tactics
open LambdaCalculusCore

let typing_terms_thm = lambda_thm "forall e env t : term. (Typing e env t) => (Term e)"

let typing_terms =
  proof' typing_terms_thm
  |> by_induction "e0" "IH"
  |> intro %> intro
  |> intros' ["He"; ""]
  |> intros' ["Ha"; "a"; ""] %> case "var" %> exists "a" %> by_solver
  |> intros' ["Hlam"; "a"; "e_a"; "t1"; "t2"; ""; ""; ""]
     %> case "lam"
     %> exists "a"
     %> exists "e_a"
     %> by_solver
     %> apply_assm_specialized "IH" ["e_a"; "cons a t1 env"; "t2"]
     %> by_solver
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists "e1"
     %> exists "e2"
     %> by_solver
     %> destruct_goal
  |> apply_assm_specialized "IH" ["e1"; "env"; "arrow t2 t"] %> by_solver %> apply_assm "Happ_1"
  |> apply_assm_specialized "IH" ["e2"; "env"; "t2"] %> by_solver %> apply_assm "Happ_2"
  |> qed

let canonical_form'_thm =
  lambda_thm
  $ unwords
      [ "forall v t :term."
      ; " (Value v) =>"
      ; " (Typing v nil t) =>"
      ; " (exists a :atom. exists e t1 t2 :term."
      ; "   [v = lam (a.e)] ∧ [t = arrow t1 t2] ∧ (Typing e {cons a t1 nil} t2))" ]

let canonical_form' =
  proof' canonical_form'_thm
  |> intros ["v"; "t"; "Hv"]
  |> destr_intro
  |> intros' ["contra"; "a"; ""]
     %> ex_falso
     %> apply_thm_specialized LambdaCalculusEnv.empty_contradiction ["a"; "t"]
     %> apply_assm "contra"
  |> intros' ["Hlam"; "a"; "e"; "t1"; "t2"; ""; ""; ""]
     %> exists' ["a"; "e"; "t1"; "t2"]
     %> repeat by_solver
     %> assumption
  |> intros' ["contra"; "e1"; "e2"; "t2"; ""]
     %> destruct_assm "Hv"
     %> (intros' ["contra_var"; "a"] %> discriminate)
     %> (intros' ["contra_lam"; "a"; "e"; ""] %> discriminate)
  |> qed

let canonical_form_thm =
  lambda_thm
  $ unwords
      [ "forall v t :term."
      ; " (Value v) =>"
      ; " (Typing v nil t) =>"
      ; " (exists a :atom. exists e :term. [v = lam (a.e)] ∧ (Term e))" ]

let canonical_form =
  proof' canonical_form_thm
  |> intros ["v"; "t"; "Hv"; "Ht"]
  |> destruct_assm "Ht"
  |> intros' ["contra"; "a"; ""]
     %> ex_falso
     %> apply_thm_specialized LambdaCalculusEnv.empty_contradiction ["a"; "t"]
     %> apply_assm "contra"
  |> intros' ["Hlam"; "a"; "e"; "t1"; "t2"; ""; ""; ""]
     %> exists' ["a"; "e"]
     %> by_solver
     %> apply_thm_specialized typing_terms ["e"; "cons a t1 nil"; "t2"]
     %> assumption
  |> intros' ["contra"; "e1"; "e2"; "t2"; ""]
     %> ex_falso
     %> destruct_assm "Hv"
     %> (intros' ["contra_var"; "a"] %> discriminate)
     %> (intros' ["contra_lam"; "a"; "e"; ""] %> discriminate)
  |> qed

let lambda_typing_inversion_thm =
  lambda_thm
  $ unwords
      [ "forall a : atom. forall e env t1 t2 : term."
      ; " (Typing {lam (a.e)} env {arrow t1 t2}) =>"
      ; "  (Typing e {cons a t1 env} t2)" ]

let lambda_typing_inversion =
  proof' lambda_typing_inversion_thm
  |> repeat intro %> destr_intro
  |> intros' ["contra"; "_"; ""] %> discriminate (* lam (a.e) is not a var *)
  |> intros' ["Hlam"; "b"; "e_b"; "t1b"; "t2b"; ""; ""; ""]
     %> apply_thm_specialized LambdaCalculusEnv.swap_lambda_typing ["b"; "e_b"; "a"; "e"; "env"; "t1"; "t2"]
     (* [b.e_b = a.e] => Typing e_b {cons b t1 env} t2 => Typing e {cons a t1 env} t2 *)
     %> by_solver
     %> assumption
  |> intros' ["contra"; "_e1"; "_e2"; "_t2"; ""] %> discriminate (* lam (a.e) is not an app *)
  |> qed
