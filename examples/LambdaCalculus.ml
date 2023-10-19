open Nominal.Prelude
open Nominal.Prover
open Nominal.Tactics
open LambdaCalculusCore

let progress_thm = lambda_thm "forall e t :term. (Typing e nil t) => (Progressive e)"

(* To show progress we will need one non-trivial lemma:                                 *)
(* 1. (Canonical forms):                                                                *)
(*   Every closed value is an abstraction of arrow type,                                *)
(*     i.e. (Value v) and (Typing v nil t) implies [v = lam (a.e)] /\ [t = arrow t1 t2] *)
(* And two trivial lemma:                                                               *)
(* 2. (Variable in empty environment contradiction):                                    *)
(*   It's impossible for a variable to occur in empty environment,                      *)
(*     i.e. (InEnv nil a t) is always false                                             *)
(* 3. (Subst exists):                                                                   *)
(*   In every term any variable can be substituted for any value,                       *)
(*     i.e. (Value v) and (Term e) implies ∃ e' : term. (Sub e a v e')                  *)
let progress =
  proof' progress_thm
  |> by_induction "e0" "IH" %> intro %> intro'
  |> intros' ["Ha"; "a"; ""] (* e is a var in empty env - contradiction *)
     %> ex_falso
     %> apply_thm_spec LambdaCalculusEnv.empty_contradiction ["a"; "t"]
     %> assumption
  |> intros' ["Hlam"; "a"; "e_a"; "t1"; "t2"; ""] (* e is a lambda - value *)
     %> case "value"
     %> case "lam"
     %> exists' ["a"; "e_a"]
     %> solve
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     (* e is an application - steps *) %> case "steps"
     %> (add_assm_parse "He1" "Progressive e1" %> apply_assm_spec "IH" ["e1"; "arrow t2 t"] %> solve)
     %> (add_assm_parse "He2" "Progressive e2" %> apply_assm_spec "IH" ["e2"; "t2"] %> solve)
  |> destruct_assm "He1"
     %> intros ["Hv1"]
     %> destruct_assm "He2"
     %> intros ["Hv2"] (* Value e1, Value e2 *)
     %> ( add_assm_thm_spec "He1lam" LambdaCalculusUtils.canonical_form ["e1"; "arrow t2 t"]
        %> apply_in_assm "He1lam" "Hv1"
        %> apply_in_assm "He1lam" "Happ_1"
        %> destruct_assm' "He1lam" ["a"; "e_a"; ""] (* He1lam: [e1 = lam (a.e_a)] ∧ (Term e_a) *) )
     %> ( add_assm_thm_spec "He_a" LambdaCalculusSub.subst_exists ["a"; "e2"; "e_a"]
        %> apply_in_assm "He_a" "Hv2"
        %> apply_in_assm "He_a" "He1lam"
        %> destruct_assm' "He_a" ["e_a'"] (* He_a: Sub e_a a e2 e_a' *) )
     %> exists "e_a'"
     %> case "app"
     %> exists' ["a"; "e_a"; "e2"]
     %> solve
     %> destruct_goal
     %> apply_assm "Hv2"
     %> apply_assm "He_a"
  |> intros' ["Hs2"; "e2'"] (* Value e1, Steps e2 e2' *)
     %> exists "app e1 e2'"
     %> case "app_r"
     %> exists' ["e1"; "e2"; "e2'"]
     %> repeat solve
     %> destruct_goal
     %> apply_assm "Hv1"
     %> apply_assm "Hs2"
  |> intros' ["Hs1"; "e1'"] (* Steps e1 *)
     %> exists "app e1' e2"
     %> case "app_l"
     %> exists' ["e1"; "e1'"; "e2"]
     %> repeat solve
     %> apply_assm "Hs1"
  |> apply_assm "Happ_2" %> apply_assm "Happ_1"
  |> qed

let preservation_thm = lambda_thm "forall e e' env t :term. (Typing e env t) => (Steps e e') => (Typing e' env t)"

(* To show preservation we will need one non-trivial lemma:                                        *)
(* 1. (Sub lemma):                                                                                 *)
(*   Substituting var from env for value of same type preserves typing,                            *)
(*     i.e. (Typing e {cons a ta env} t) and (Typing v env ta) implies (Typing {e (a -> v)} env t) *)
(* And one trivial lemma:                                                                          *)
(* 2. (Lambda typing inversion lemma):                                                             *)
(*   Deduce typing of a body in env with added argument from the typing of whole abstraction       *)
(*     i.e. (Typing e_a {cons a t1 env} t2) and [b # a e_a] implies (Typing e_b {cons b t1} t2)    *)
let preservation =
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
     %> solve
     %> destruct_goal
     (* Typing e1 env {arrow t2 t} => Steps e1 e1' => Typing e1' env {arrow t2 t}*)
     %> apply_assm_spec "IH" ["e1"; "e1'"; "env"; "arrow t2 t"]
     %> solve
     %> apply_assm "Happ_1"
     %> apply_assm "He1"
     (* Typing e2 env t2 *)
     %> apply_assm "Happ_2"
  |> intros' ["He2"; "v1"; "e2"; "e2'"; ""; ""; ""] (* e = app v1 e2, Value e1, Steps e2 e2' *)
     %> deduce_app_typing
     %> case "app"
     %> exists' ["v1"; "e2'"; "t2"]
     %> solve
     %> destruct_goal
     (* Typing e1 env {arrow t2 t} *)
     %> apply_assm "Happ_1"
     (* Typing e2 env t2 => Steps e2 e2' => Typing e2' env t2*)
     %> apply_assm_spec "IH" ["e2"; "e2'"; "env"; "t2"]
     %> solve
     %> apply_assm "Happ_2"
     %> apply_assm "He2_2"
  |> intros' ["Hbeta"; "a"; "e_a"; "v"; ""; ""] (* e = app (lam (a.e_a)) v, Value v *)
     %> deduce_app_typing
     %> apply_thm_spec LambdaCalculusSub.sub_lemma ["e_a"; "env"; "t"; "a"; "t2"; "v"; "e'"]
        (* Typing v env t2 => Typing e_a {cons a t2 env} t => Sub e_a a v e' => Typing e' env t *)
     %> apply_assm "Happ_2"
     %> apply_thm_spec LambdaCalculusUtils.lambda_typing_inversion ["a"; "e_a"; "env"; "t2"; "t"]
        (* Typing {lam (a.e_a)} env {arrow t2 t} => Typing e_a {cons a t2 env} t *)
     %> apply_assm "Happ_1"
     %> apply_assm "Hbeta_2"
  |> qed
