open Nominal.Prelude
open Nominal.Prover
open Nominal.Tactics
open LambdaCalculusCore
open LambdaCalculusEnv

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

let canonical_form_thm =
  lambda_thm
  $ unwords
      [ "forall v t :term."
      ; " (Value v) =>"
      ; " (Typing v nil t) =>"
      ; " (exists a :atom. exists e :term. [v = lam (a.e)] ∧ (Term e))"
      ; " ∧"
      ; " (exists t1 t2 :term. [t = arrow t1 t2])" ]

let canonical_form =
  proof' canonical_form_thm
  |> intro %> intro
  |> intros ["Hv"; "Ht"] %> destruct_assm "Ht"
  |> intros' ["contra"; "a"; ""]
     %> ex_falso
     %> apply_thm_specialized empty_contradiction ["a"; "t"]
     %> apply_assm "contra"
  |> intros' ["Hlam"; "a"; "e"; "t1"; "t2"; ""; ""; ""]
  |> destruct_goal
  |> exists "a"
     %> exists "e"
     %> by_solver
     %> apply_thm_specialized typing_terms ["e"; "cons a t1 nil"; "t2"]
     %> assumption
     %> exists "t1"
     %> exists "t2"
     %> by_solver
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""] %> ex_falso %> destruct_assm "Hv"
  |> intros' ["Ha"; "a"] %> by_solver
  |> intros' ["Hlam"; "a"; "e"; ""] %> by_solver
  |> qed

let canonical_form'_thm =
  lambda_thm
  $ unwords
      [ "forall v t1 t2 :term."
      ; " (Value v) =>"
      ; " (Typing v nil {arrow t1 t2}) =>"
      ; " (exists a :atom. exists e :term. [v = lam (a.e)] ∧ (Term e))" ]

let canonical_form' =
  proof' canonical_form'_thm
  |> intro %> intro %> intro
  |> intros ["Hv"; "Ht"]
  |> add_assumption_parse "H"
       (unwords
          [ "(exists a :atom. exists e :term. [v = lam (a.e)] ∧ (Term e))"
          ; "∧"
          ; "(exists t1' t2' :term. [arrow t1 t2 = arrow t1' t2'])" ] )
  |> destruct_assm' "H" [""]
  |> assumption
  |> apply_thm_specialized canonical_form ["v"; "arrow t1 t2"] %> apply_assm "Hv" %> apply_assm "Ht"
  |> qed
