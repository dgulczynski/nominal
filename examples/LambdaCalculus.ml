open Nominal.Prelude
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
     %> case "value"
     %> case "lam"
     %> exists' ["a"; "e_a"]
     %> by_solver
     %> apply_thm_specialized LambdaCalculusUtils.typing_terms ["e_a"; "cons a t1 nil"; "t2"]
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""] (* e is an application - steps *)
  |> add_assumption_parse "He1" "Progressive e1"
  |> add_assumption_parse "He2" "Progressive e2"
  |> destruct_assm "He1"
     %> intros ["Hv1"]
     %> destruct_assm "He2"
     %> intros ["Hv2"] (* Value e1, Value e2 *)
     %> ( add_assumption_thm_specialized "He1lam" LambdaCalculusUtils.canonical_form' ["e1"; "t2"; "t"]
        %> apply_in_assm "He1lam" "Hv1"
        %> apply_in_assm "He1lam" "Happ_1"
        %> destruct_assm' "He1lam" ["a"; "e_a"; ""] (* He1lam: [e1 = lam (a.e_a)] ∧ (Term e_a) *) )
     %> ( add_assumption_thm_specialized "He_a" LambdaCalculusSub.subst_exists ["a"; "e2"; "e_a"]
        %> apply_in_assm "He_a" "Hv2"
        %> apply_in_assm "He_a" "He1lam"
        %> destruct_assm' "He_a" ["e_a'"] (* He_a: Sub e_a a e2 e_a' *) )
     %> case "steps"
     %> exists "e_a'"
     %> case "app"
     %> exists' ["a"; "e_a"; "e2"]
     %> by_solver
     %> destruct_goal
     %> apply_assm "Hv2"
     %> apply_assm "He_a"
  |> intros' ["Hs2"; "e2'"] (* Value e1, Steps e2 e2' *)
     %> case "steps"
     %> exists "app e1 e2'"
     %> case "app_r"
     %> exists' ["e1"; "e2"; "e2'"]
     %> by_solver
     %> by_solver
     %> destruct_goal
     %> apply_assm "Hv1"
     %> apply_assm "Hs2"
  |> intros' ["Hs1"; "e1'"] (* Steps e1 *)
     %> case "steps"
     %> exists "app e1' e2"
     %> case "app_l"
     %> exists' ["e1"; "e1'"; "e2"]
     %> by_solver
     %> by_solver
     %> apply_assm "Hs1"
  |> apply_assm_specialized "IH" ["e2"; "t2"] %> by_solver %> apply_assm "Happ_2" (* Progressive e2 *)
  |> apply_assm_specialized "IH" ["e1"; "arrow t2 t"] %> by_solver %> apply_assm "Happ_1" (* Progressive e1 *)
  |> qed

let preservation_thm = lambda_thm "forall e e' env t :term. (Typing e env t) => (Steps e e') => (Typing e' env t)"

(* To show preservation we will need two non-trivial lemmas: *)
(* 1. (Sub lemma): Substituting var from env for value of same type preserves typing, *)
(*     i.e. (Typing e {cons a ta env} t) and (Typing v env ta) implies (Typing {e (a -> v)} env t) *)
(* 2. (Swap lambda typing): Swapping argument of lambda abstraction preserves typing *)
(*     i.e. (Typing e_a {cons a t1 env} t2) and [b # a e_a] implies (Typing e_b {cons b t1} t2) *)
let preservation =
  let contra_var = intros' ["contra"; "_"; ""] %> discriminate in
  let contra_app = intros' ["contra"; "_e1"; "_e2"; "_t2"; ""] %> discriminate in
  let deduce_app_typing =
    destruct_assm "Htyp"
    %> (intros' ["contra"; "_"; ""] %> discriminate)
    %> (intros' ["contra"; "_"; "e_"; "t1"; "t2"; ""] %> discriminate)
    %> intros' ["Happ"; "e_1"; "e_2"; "t2"; ""; ""]
  in
  proof' preservation_thm
  |> by_induction "e0" "IH"
  |> intro %> intro %> intro %> intros ["Htyp"; "Hstep"]
  |> destruct_assm "Hstep"
  |> intros' ["He1"; "e1"; "e1'"; "e2"; ""; ""] (* e = app e1 e2, Steps e1 e1' *)
     %> deduce_app_typing
     %> case "app"
     %> exists' ["e1'"; "e2"; "t2"]
     %> by_solver
     %> destruct_goal
     (* Typing e1 env {arrow t2 t} => Steps e1 e1' => Typing e1' env {arrow t2 t}*)
     %> apply_assm_specialized "IH" ["e1"; "e1'"; "env"; "arrow t2 t"]
     %> by_solver
     %> apply_assm "Happ_1"
     %> apply_assm "He1"
     (* Typing e2 env t2 *)
     %> apply_assm "Happ_2"
  |> intros' ["He2"; "v1"; "e2"; "e2'"; ""; ""; ""] (* e = app v1 e2, Value e1, Steps e2 e2' *)
     %> deduce_app_typing
     %> case "app"
     %> exists' ["v1"; "e2'"; "t2"]
     %> by_solver
     %> destruct_goal
     (* Typing e1 env {arrow t2 t} *)
     %> apply_assm "Happ_1"
     (* Typing e2 env t2 => Steps e2 e2' => Typing e2' env t2*)
     %> apply_assm_specialized "IH" ["e2"; "e2'"; "env"; "t2"]
     %> by_solver
     %> apply_assm "Happ_2"
     %> apply_assm "He2_2"
  |> intros' ["Hbeta"; "a"; "e_a"; "v"; ""; ""] (* e = app (lam (a.e_a)) v, Value v *)
     %> deduce_app_typing
     %> destruct_assm "Happ_1"
     %> contra_var (* e_1 =/= var *)
     %> intros' ["Hlam"; "b"; "e_b"; "t1b"; "t2b"; ""; ""; ""] (* e_1 = b.e_b *)
     (* Typing v env t2 => Typing e_a {cons a t2 env} t => Sub e_a a v e' => Typing e' env t *)
     %> apply_thm_specialized LambdaCalculusSub.sub_lemma ["e_a"; "env"; "t"; "a"; "t2"; "v"; "e'"]
     %> apply_assm "Happ_2" (* Typing v env t2 *)
     %> compare_atoms "a" "b" (* Typing e_a cons a t2 env t *)
     %> destr_intro
     (* a = b *) %> apply_assm "Hlam_2"
     %> destr_intro (* a =/= b *)
     (* [a # b e_b] => Typing e_b {cons b t2 env} t => Typing {[b a]e_b} {cons a t2 env} t *)
     %> apply_thm_specialized LambdaCalculusEnv.swap_lambda_typing ["e_b"; "env"; "t"; "b"; "a"; "t2"]
     %> by_solver
     %> apply_assm "Hlam_2"
     %> apply_assm "Hbeta_2" (* Sub e_a a v e' *)
     %> contra_app (* e_1 =/= app _ _ *)
  |> qed
