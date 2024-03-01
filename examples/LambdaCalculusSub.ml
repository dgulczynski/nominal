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
  let contra_sub_lam = intros' ["contra"; "_"; "e_"; "e_'"; ""; ""] %> discriminate in
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
        %> solve
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
        %> repeat solve
        %> destruct_goal
        %> assumption
        %> apply_assm_spec "IH" ["e_c"; "cons c t1 env"; "t2"; "a"; "ta"; "v"; "e_c'"]
        %> solve
        %> (apply_thm_spec LambdaCalculusEnv.cons_fresh_typing ["v"; "env"; "ta"; "c"; "t1"] %> solve %> apply_assm "Hv")
        %> ( apply_thm_spec LambdaCalculusEnv.typing_env_shuffle ["e_c"; "env"; "t2"; "c"; "t1"; "a"; "ta"]
           %> solve
           %> apply_thm_spec LambdaCalculusEnv.swap_lambda_typing ["b"; "e_b"; "c"; "e_c"; "cons a ta env"; "t1"; "t2"]
           %> solve
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
        %> solve
        %> destruct_goal
        %> ( apply_assm_spec "IH" ["e1"; "env"; "arrow t2 t"; "a"; "ta"; "v"; "e1'"]
           %> solve
           %> apply_assm "Hv"
           %> apply_assm "Happ_1"
           %> apply_assm "Hsub_1" )
        %> ( apply_assm_spec "IH" ["e2"; "env"; "t2"; "a"; "ta"; "v"; "e2'"]
           %> solve
           %> apply_assm "Hv"
           %> apply_assm "Happ_2"
           %> apply_assm "Hsub_2" ) )
  |> qed

(* let sub_lemma' = (* let contra_sub_var = intros' ["contra"; "_b"; ""; ""; ""] %> discriminate in *) (* let contra_var
   = intros' ["contra"; "_"; ""] %> discriminate in *) let contra_sub_lam = intros' ["contra"; "_"; "e_"; "e_'"; ""; ""]
   %> discriminate in let contra_sub_app = intros' ["contra"; "e1"; "e2"; "e1'"; "e2'"; ""; ""] %> discriminate in let p
   = unwords [ "fun e :term ->" ; " forall env t : term. forall a : atom. forall ta v e' : term." ; " (Typing v env ta)
   =>" ; " (Typing e {cons a ta env} t) =>" ; " (Sub e a v e') =>" ; " Typing e' env t" ] in let intro_assms = compute
   %> repeat intro %> intros ["Hv"; "He"; "Hsub"] in proof' sub_lemma_thm |> intros ["e"] %> apply_thm_spec lambda_ind
   [p; "e"; "e"] |> intros ["b"] %> intro_assms %> destruct_assm "Hsub" %> intros' ["Heq"; ""] %> destruct_assm "He" %>
   intros' ["Heq'"; "b'"; ""; ""] %> intros' ["Heq''"; "env''"] %> apply_assm "Hv" %> intros' ["contra"; "b''"; "t'";
   "env''"; ""; ""] %> discriminate %> contra_sub_lam %> contra_sub_app *)

let subst_exists_thm =
  lambda_thm
    {|
      forall a :atom.
      forall v :term. (Value v) =>
      forall e :term. (Term e) =>
        exists e' :term. (Sub e a v e')
     |}

let subst_exists =
  proof' subst_exists_thm
  |> intros ["a"; "v"; "Hv"] %> by_induction "e0" "IH" %> intro'
  |> intros' ["Hb"; "b"; ""]
     %> compare_atoms "a" "b"
     %> (intro' %> exists "v" %> case "var_same" %> repeat solve)
     %> (intro' %> exists "b" %> case "var_diff" %> exists "b" %> repeat solve)
  |> intros' ["Hlam"; "b"; "e_b"; ""]
     %> get_fresh_atom "c" "a v e_b"
     %> (add_assm_parse "He_c" "exists e_c:term. Sub {[b c]e_b} a v e_c" %> apply_assm_spec "IH" ["[c b]e_b"] %> solve)
     %> destruct_assm' "He_c" ["e_c"]
     %> exists "lam (c.e_c)"
     %> case "lam"
     %> exists' ["c"; "[c b]e_b"; "e_c"]
     %> repeat solve
     %> assumption
     %> apply_thm_spec swap_term_lemma ["e_b"; "c"; "b"]
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; ""; ""]
     %> (add_assm_parse "He1" "exists e1':term. Sub e1 a v e1'" %> apply_assm_spec "IH" ["e1"] %> solve)
     %> (add_assm_parse "He2" "exists e2':term. Sub e2 a v e2'" %> apply_assm_spec "IH" ["e2"] %> solve)
     %> destruct_assm "He1"
     %> destruct_assm "He2"
     %> exists "app e1' e2'"
     %> case "app"
     %> exists' ["e1"; "e2"; "e1'"; "e2'"]
     %> repeat solve
     %> destruct_goal
     %> apply_assm "He1"
     %> apply_assm "He2"
     %> apply_assm "Happ_2"
     %> apply_assm "Happ_1"
  |> qed

(* Nawet spoko dowód z egzystencjalnym *)
let subst_exists'' =
  proof' subst_exists_thm
  |> intros ["a"; "v"; "Hv"] %> apply_thm_spec lambda_ind' ["fun e:term -> ∃ e' : term. Sub e a v e'"]
  |> intros' ["b"]
     %> compare_atoms "a" "b"
     %> (intros ["Heq"] %> exists "v" %> case "var_same" %> repeat solve)
     %> (intros ["Hdiff"] %> exists "b" %> case "var_diff" %> exists "b" %> repeat solve)
  |> intros ["e1"; "e2"; "He1"; "He2"]
     %> intros' ["IHe1"; "e1'"]
     %> intros' ["IHe2"; "e2'"]
     %> exists "app e1' e2'"
     %> case "app"
     %> exists' ["e1"; "e2"; "e1'"; "e2'"]
     %> repeat solve
     %> destruct_goal
     %> apply_assm "IHe1"
     %> apply_assm "IHe2"
  |> intros ["b"; "e_b"; "He_b"; "IHlam"]
     %> specialize_assm "IHlam" "IHlam" ["a v b e_b"]
     %> destruct_assm' "IHlam" ["c"; "e_c"; ""]
     %> destruct_assm' "IHlam_2" [""; ""; "e_c'"]
     %> exists "lam (c.e_c')"
     %> case "lam"
     %> exists' ["c"; "e_c"; "e_c'"]
     %> repeat solve
     %> apply_assm "IHlam_2"
  |> qed

let subst_exists' =
  proof' subst_exists_thm
  |> intros ["a"; "v"; "Hv"; "e"]
     %> apply_thm_spec lambda_ind ["fun e:term -> exists e' :term. Sub e a v e'"; "e a v"; "e"]
  |> intros ["b"]
     %> compare_atoms "a" "b"
     %> intro'
     %> exists "v"
     %> case "var_same"
     %> repeat solve
     %> intro'
     %> exists "b"
     %> case "var_diff"
     %> exists "b"
     %> repeat solve
  |> intros ["e1"; "e2"; "He1"; "He1'"; "He2"; "He2'"]
     %> destruct_assm' "He1'" ["e1'"]
     %> destruct_assm' "He2'" ["e2'"]
     %> exists "app e1' e2'"
     %> case "app"
     %> exists' ["e1"; "e2"; "e1'"; "e2'"]
     %> repeat solve
     %> destruct_goal
     %> apply_assm "He1'"
     %> apply_assm "He2'"
  |> intros ["b"; "e_b"]
     %> intro
     %> intros ["He_b"]
     %> intros' ["He_b'"; "e_b'"]
     %> exists "lam (b.e_b')"
     %> case "lam"
     %> exists' ["b"; "e_b"; "e_b'"]
     %> repeat solve
     %> apply_assm "He_b'"
  |> qed

let contra_sub_var = intros' ["contra"; "_b"; ""; ""; ""] %> discriminate

let contra_var = intros' ["contra"; "_"; ""] %> discriminate

let contra_sub_lam = intros' ["contra"; "_"; "e_"; "e_'"; ""; ""] %> discriminate

let contra_sub_app = intros' ["contra"; "e1"; "e2"; "e1'"; "e2'"; ""; ""] %> discriminate

(* let deduce_lam_typing_thm = lambda_thm "forall a:atom. forall e:term." *)
let sub_lemma'_thm =
  lambda_thm
  $ unwords
      [ "forall e env t :term."
      ; "forall a : atom. forall ta :term."
      ; "forall v e' :term."
      ; " (Term e) =>"
      ; " (Typing v env ta) =>"
      ; " (Typing e {cons a ta env} t) =>"
      ; " (Sub e a v e') =>"
      ; "   (Typing e' env t)" ]

let sub_lemma' =
  let contra_sub_var = intros' ["contra"; "_b"; ""; ""; ""] %> discriminate in
  let contra_var = intros' ["contra"; "_"; ""] %> discriminate in
  let contra_sub_lam = intros' ["contra"; "_"; "e_"; "e_'"; ""; ""] %> discriminate in
  let contra_sub_app = intros' ["contra"; "e1"; "e2"; "e1'"; "e2'"; ""; ""] %> discriminate in
  let sub_lemma_var_thm =
    lambda_thm
    $ unlines
        [ "∀ b a :atom. ∀ ta v : term. ∀ env t e' : term. "
        ; "     (Typing v env ta)                                    "
        ; "  => (Typing {b} {cons a ta env} t)                       "
        ; "  => (Sub {b} a v e')                                     "
        ; "  => Typing e' env t" ]
  in
  let sub_lemma_var =
    proof' sub_lemma_var_thm
    |> intros ["b"; "a"; "ta"; "v"; "env"; "t"; "e'"; "Hv"; "Htyp"; "Hsub"]
    |> destruct_assm "Hsub"
    |> intros' ["Heq"; ""; ""]
       %> destruct_assm "Htyp"
       %> (intros' ["Hb"; "env'"; ""] %> destruct_assm "Hb" %> intros' ["Heq"; "env''"; ""] %> apply_assm "Hv")
       %> (intros' ["Hdiff"; "b'"; "t'"; "env''"; ""; ""] %> discriminate)
       %> contra_sub_lam
       %> contra_sub_app
    |> intros' ["Hb"; "b'"; ""; ""]
       %> destruct_assm "Htyp"
       %> (intros' ["Hb'"; "b''"; ""] %> destruct_assm "Hb'" %> contra_var)
       %> (intros' ["Hdiff"; "a'"; "t'"; "env'"; ""; ""] %> case "var" %> exists "b''" %> solve %> apply_assm "Hdiff")
       %> contra_sub_lam
       %> contra_sub_app
       %> contra_sub_lam
       %> contra_sub_app
    |> qed
  in
  let sub_lemma_app_thm =
    lambda_thm
    $ unlines
        [ "∀ t1 t2 : term. ∀ a : atom. ∀ ta v : term.   "
        ; "        (Term t1)                                  "
        ; "     => (Term t2)                                  "
        ; "     => (∀ env t e' : term.                        "
        ; "             (Typing v env ta)                     "
        ; "          => (Typing t1 {cons a ta env} t)         "
        ; "          => (Sub t1 a v e')                       "
        ; "          => Typing e' env t)                      "
        ; "     => (∀ env t e' : term.                        "
        ; "             (Typing v env ta)                     "
        ; "          => (Typing t2 {cons a ta env} t)         "
        ; "          => (Sub t2 a v e')                       "
        ; "          => Typing e' env t)                      "
        ; "     => ∀ env t e' : term.                         "
        ; "             (Typing v env ta)                     "
        ; "          => (Typing {app t1 t2} {cons a ta env} t)"
        ; "          => (Sub {app t1 t2} a v e')              "
        ; "          => Typing e' env t" ]
  in
  let sub_lemma_app =
    proof' sub_lemma_app_thm
    |> intros ["e1"; "e2"; "a"; "ta"; "v"; "He1"; "He2"; "IHe1"; "IHe2"; "env"; "t"; "e'"; "Hv"; "Htyp"; "Hsub"]
       %> destruct_assm "Htyp"
       %> contra_var
       %> contra_sub_lam
       %> ( intros' ["He'"; "e1'"; "e2'"; "t1"; "t2"; ""; ""]
          %> destruct_assm "Hsub"
          %> contra_var
          %> contra_sub_var
          %> contra_sub_lam
          %> intros' ["Hsub"; "e1''"; "e2''"; "s1"; "s2"; ""; ""; ""]
          %> (case "app" %> exists' ["s1"; "s2"; "t1"] %> solve)
          %> destruct_goal
          %> ( apply_assm_spec "IHe1" ["env"; "arrow t1 t"; "s1"]
             %> (apply_assm "Hv" %> apply_assm "He'_1" %> apply_assm "Hsub_1") )
          %> ( apply_assm_spec "IHe2" ["env"; "t1"; "s2"]
             %> (apply_assm "Hv" %> apply_assm "He'_2" %> apply_assm "Hsub_2") ) )
    |> qed
  in
  let sub_property =
    unwords
      [ "fun e:term ->                      "
      ; "  forall env t e' : term.          "
      ; "    (Typing v env ta) =>           "
      ; "    (Typing e {cons a ta env} t) =>"
      ; "    (Sub e a v e') =>              "
      ; "      Typing e' env t" ]
  in
  proof' sub_lemma'_thm
  |> repeat intro
     %> intros ["He"]
     %> generalize "e'"
     %> generalize "t"
     %> generalize "env"
     %> apply_thm_spec lambda_ind'' [sub_property; "e"]
  |> intros ["b"] %> apply_thm_spec sub_lemma_var ["b"; "a"; "ta"; "v"]
  |> intros ["e1"; "e2"] %> apply_thm_spec sub_lemma_app ["e1"; "e2"; "a"; "ta"; "v"]
  |> intros ["b"; "e_b"]
     %> intros ["He_b"; "IHe_b"; "env"; "t"; "e'"; "Hv"; "Htyp"; "Hsub"]
     %> destruct_assm "Hsub"
     %> contra_var
     %> contra_sub_var
     %> intros' ["Hsub"; "d"; "e_d"; "e_d'"; ""; ""; ""; ""]
     %> add_assm_thm_spec "Htyp'" LambdaCalculusUtils.lambda_typing_inversion' ["d"; "e_d"; "cons a ta env"; "t"]
     %> apply_in_assm "Htyp'" "Htyp"
     %> destruct_assm' "Htyp'" ["t1"; "t2"; ""; ""]
     %> case "lam"
     %> exists' ["d"; "e_d'"; "t1"; "t2"]
     %> solve
     %> solve
     %> destruct_goal
     %> assumption
     %> apply_assm_spec "IHe_b" ["d.d"; "d"; "e_d"; "cons d t1 env"; "t2"; "e_d'"]
     %> solve
     %> solve
     %> (apply_thm_spec LambdaCalculusEnv.cons_fresh_typing ["v"; "env"; "ta"; "d"; "t1"] %> solve %> assumption)
     %> ( apply_thm_spec LambdaCalculusEnv.typing_env_shuffle ["e_d"; "env"; "t2"; "d"; "t1"; "a"; "ta"]
        %> solve
        %> assumption )
     %> assumption
     %> contra_sub_app
  |> apply_assm "He"
  |> qed
