open Nominal.Prelude
open Nominal.Prover
open Nominal.Tactics
open LambdaCalculusCore

let env_inclusion_cons_both_thm =
  lambda_thm
  $ unwords
      [ "forall env1 env2 : term."
      ; "forall a' : atom. forall t' : term."
      ; "(EnvInclusion env1 env2) =>"
      ; "(EnvInclusion {cons a' t' env1} {cons a' t' env2})" ]

let env_inclusion_cons_both =
  proof' env_inclusion_cons_both_thm
  |> repeat intro
  |> intros ["Hinclusion"]
  |> compute %> intro %> intro %> intros' ["Hinenv"; ""]
  |> intros' ["Hcurrent"; "env3"] %> case "current" %> exists "env2" %> solve
  |> intros' ["Hnext"; "c"; "tc"; "env3"; ""; ""]
     %> case "next"
     %> exists' ["c"; "tc"; "env2"]
     %> solve
     %> solve
     %> apply_assm_spec "Hinclusion" ["a"; "t"]
     %> apply_assm "Hnext"
  |> qed

let weakening_lemma_thm =
  lambda_thm "forall e env1 t env2 : term. (Typing e env1 t) => (EnvInclusion env1 env2) => (Typing e env2 t)"

let weakening_lemma =
  proof' weakening_lemma_thm
  |> by_induction "e0" "IH"
  |> repeat intro
  |> intros ["Htyp"; "Hinc"] %> destruct_assm "Htyp"
  |> intros' ["Hb"; "b"; ""] %> case "var" %> exists "b" %> solve %> apply_assm_spec "Hinc" ["b"; "t"] %> assumption
  |> intros' ["Hlam"; "b"; "e_b"; "t1"; "t2"; ""; ""; ""]
     %> case "lam"
     %> exists' ["b"; "e_b"; "t1"; "t2"]
     %> solve
     %> solve
     %> destruct_goal
     %> assumption
     %> apply_assm_spec "IH" ["e_b"; "cons b t1 env1"; "t2"; "cons b t1 env2"]
     %> solve
     %> assumption
     %> apply_thm_spec env_inclusion_cons_both ["env1"; "env2"; "b"; "t1"]
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["e1"; "e2"; "t2"]
     %> solve
     %> destruct_goal
     %> apply_assm_spec "IH" ["e1"; "env1"; "arrow t2 t"; "env2"]
     %> solve
     %> assumption
     %> assumption
     %> apply_assm_spec "IH" ["e2"; "env1"; "t2"; "env2"]
     %> solve
     %> assumption
     %> assumption
  |> qed

let shadow_thm =
  lambda_thm
  $ unwords
      [ "forall a : atom.                        "
      ; "forall t1 t2 env : term.                "
      ; "EnvInclusion {cons a t1 (cons a t2 env)}"
      ; "             {cons a t1            env }" ]

let shadow =
  proof' shadow_thm
  |> repeat intro
  |> compute %> intros ["b"; "tb"] %> intro'
  |> intros' ["Hcurrent"; "env'"; ""] %> case "current" %> exists "env" %> solve
  |> intros' ["Hnext"; "c"; "tc"; "envc"; ""; ""; ""]
  |> intros' ["contra"; "envc'"] %> discriminate
  |> intros' ["Hnext"; "d"; "td"; "envd"; ""; ""]
     %> case "next"
     %> exists' ["a"; "t1"; "env"]
     %> solve
     %> solve
     %> assumption
  |> qed

let shadow'_thm =
  lambda_thm
  $ unwords
      [ "forall a : atom.                        "
      ; "forall t1 t2 env : term.                "
      ; "EnvInclusion {cons a t1            env }"
      ; "             {cons a t1 (cons a t2 env)}" ]

let shadow' =
  proof' shadow'_thm
  |> repeat intro %> compute %> intros ["b"; "tb"] %> intro'
  |> intros' ["Hcurrent"; "env'"; ""] %> case "current" %> exists "(cons a t2 env)" %> solve
  |> intros' ["Hnext"; "c"; "tc"; "envc"; ""; ""]
     %> case "next"
     %> exists' ["a"; "t1"; "cons a t2 envc"]
     %> solve
     %> solve
     %> case "next"
     %> exists' ["a"; "t2"; "envc"]
     %> solve
     %> solve
     %> assumption
  |> qed

let env_inclusion_shuffle_thm =
  lambda_thm
  $ unwords
      [ "forall a : atom. forall ta : term.        "
      ; "forall b : atom. forall tb env : term.    "
      ; "  [a =/= b] =>                            "
      ; "  EnvInclusion {cons a ta (cons b tb env)}"
      ; "               {cons b tb (cons a ta env)}" ]

let env_inclusion_shuffle =
  proof' env_inclusion_shuffle_thm
  |> repeat intro %> compute %> intros ["c"; "tc"] %> intro'
  |> intros' ["Hcurrent"; "envc"; ""]
     %> case "next"
     %> exists' ["b"; "tb"; "cons a ta env"]
     %> solve
     %> solve
     %> case "current"
     %> exists "env"
     %> solve
  |> intros' ["Hnext"; "d"; "td"; "envd"; ""; ""; ""]
  |> intros' ["H"; "envc"; ""] %> case "current" %> exists "cons a ta env" %> solve
  |> intros' ["H"; "e"; "te"; "enve"; ""; ""]
     %> case "next"
     %> exists' ["b"; "tb"; "cons a ta env"]
     %> solve
     %> solve
     %> case "next"
     %> exists' ["a"; "ta"; "enve"]
     %> solve
     %> solve
  |> assumption
  |> qed

let typing_env_shuffle_thm =
  lambda_thm
  $ unwords
      [ "forall e env t : term.                     "
      ; "forall a :atom. forall ta :term.           "
      ; "forall b :atom. forall tb :term.           "
      ; "[a =/= b] =>                               "
      ; "(Typing e {cons a ta (cons b tb env)} t) =>"
      ; "(Typing e {cons b tb (cons a ta env)} t)" ]

let typing_env_shuffle =
  proof' typing_env_shuffle_thm
  |> repeat intro
  |> intros ["H"]
     %> apply_thm_spec weakening_lemma ["e"; "cons a ta (cons b tb env)"; "t"; "cons b tb (cons a ta env)"]
     %> apply_assm "H"
     %> apply_thm_spec env_inclusion_shuffle ["a"; "ta"; "b"; "tb"; "env"]
     %> solve
  |> qed

let cons_fresh_typing_thm =
  lambda_thm
  $ unwords
      [ "forall e env t : term.          "
      ; "forall a :atom. forall ta :term."
      ; " [a # e] =>                     "
      ; " (Typing e             env t) =>"
      ; " (Typing e {cons a ta env} t)" ]

let cons_fresh_typing =
  proof' cons_fresh_typing_thm
  |> by_induction "e0" "IH" %> repeat intro %> intro'
  |> intros' ["Hb"; "b"; ""]
     %> case "var"
     %> exists "b"
     %> solve
     %> case "next"
     %> exists' ["a"; "ta"; "env"]
     %> solve
     %> solve
     %> apply_assm "Hb"
  |> intros' ["Hlam"; "b"; "e_b"; "t1"; "t2"; ""; ""; ""]
     %> case "lam"
     %> compare_atoms "a" "b"
     %> intro'
     %> exists' ["b"; "e_b"; "t1"; "t2"]
     %> solve
     %> solve
     %> destruct_goal
     %> apply_assm "Hlam_1"
     %> apply_thm_spec weakening_lemma ["e_b"; "cons b t1 env"; "t2"; "cons b t1 (cons a ta env)"]
     %> apply_assm "Hlam_2"
     %> apply_thm_spec shadow' ["b"; "t1"; "ta"; "env"]
     %> intro'
     %> exists' ["b"; "e_b"; "t1"; "t2"]
     %> solve
     %> solve
     %> destruct_goal
     %> apply_assm "Hlam_1"
     %> apply_thm_spec weakening_lemma ["e_b"; "cons a ta (cons b t1 env)"; "t2"; "cons b t1 (cons a ta env)"]
     %> apply_assm_spec "IH" ["e_b"; "cons b t1 env"; "t2"; "a"; "ta"]
     %> solve
     %> solve
     %> apply_assm "Hlam_2"
     %> apply_thm_spec env_inclusion_shuffle ["a"; "ta"; "b"; "t1"; "env"]
     %> solve
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["e1"; "e2"; "t2"]
     %> solve
     %> destruct_goal
     %> apply_assm_spec "IH" ["e1"; "env"; "arrow t2 t"; "a"; "ta"]
     %> solve
     %> solve
     %> apply_assm "Happ_1"
     %> apply_assm_spec "IH" ["e2"; "env"; "t2"; "a"; "ta"]
     %> solve
     %> solve
     %> apply_assm "Happ_2"
  |> qed

let swap_inenv_lemma_thm =
  lambda_thm
  $ unwords
      [ "forall a b c : atom. "
      ; "forall env t : term. "
      ; "[a # env] => "
      ; "(InEnv env c t) => "
      ; "(InEnv {[a b]env} ([a b]c) {[a b]t})" ]

let swap_inenv_lemma =
  proof' swap_inenv_lemma_thm
  |> intros ["a"; "b"; "c"] %> by_induction "e0" "IH" %> intro %> intro %> intro'
  |> intros' ["Hcurrent"; "env'"; ""] %> case "current" %> exists "[a b]env'" %> solve
  |> intros' ["Hnext"; "d"; "td"; "env'"; ""; ""]
     %> case "next"
     %> exists' ["[a b]d"; "[a b]td"; "[a b]env'"]
     %> solve
     %> solve
     %> apply_assm_spec "IH" ["env'"; "t"]
     %> solve
     %> solve
     %> assumption
  |> qed

let atom_fresh_in_type_thm = lambda_thm "forall a : atom. forall t: term. (Type t) => (a # t)"

let atom_fresh_in_type =
  proof' atom_fresh_in_type_thm
  |> intros ["a"]
     %> by_induction "t0" "IH"
     %> intro'
     %> intros ["Hbase"]
     %> solve
     %> intros' ["Harrow"; "t1"; "t2"; ""; ""]
     %> (add_assm_parse "Ht1" "a # t1" %> apply_assm_spec "IH" ["t1"] %> solve)
     %> (add_assm_parse "Ht2" "a # t2" %> apply_assm_spec "IH" ["t2"] %> solve)
     %> solve
     %> assumption
     %> assumption
  |> qed

let env_inclusion_refl_thm = lambda_thm "forall env : term. EnvInclusion env env"

let env_inclusion_refl = proof' env_inclusion_refl_thm |> intro %> compute %> repeat intro %> trivial |> qed

let env_inclusion_double_skip_thm =
  lambda_thm
  $ unwords
      [ "forall a :atom. forall ta :term.                        "
      ; "forall b :atom. forall tb :term.                        "
      ; "forall c :atom. forall tc :term.                        "
      ; "forall env1 env2 : term.                                "
      ; " [c # a b] =>                                           "
      ; " (EnvInclusion env1 env2) =>                            "
      ; " (EnvInclusion {cons c tc (cons a ta (cons b tb env1))} "
      ; "               {cons a ta (cons b tb (cons c tc env2))})" ]

let env_inclusion_double_skip =
  proof' env_inclusion_double_skip_thm
  |> repeat intro
  |> intros ["H"] %> compute %> intros ["d"; "td"] %> intro'
  |> intros' ["Hdc"; "envc"]
     %> case "next"
     %> exists' ["a"; "ta"; "cons b tb (cons c tc env2)"]
     %> repeat solve
     %> case "next"
     %> exists' ["b"; "tb"; "cons c tc env2"]
     %> repeat solve
     %> case "current"
     %> exists "env2"
     %> solve
  |> intros' ["Hnext"; "c'"; "tc'"; "envc'"; ""; ""; ""]
  |> intros' ["Hda"; "enva"] %> case "current" %> exists "cons b tb (cons c tc env2)" %> solve
  |> intros' ["Hnext"; "a'"; "ta'"; "enva'"; ""; ""; ""]
  |> intros' ["Hdb"; "envb"]
     %> case "next"
     %> exists' ["a"; "ta"; "cons b tb (cons c tc env2)"]
     %> repeat solve
     %> case "current"
     %> exists "cons c tc env2"
     %> solve
  |> intros' ["Hd"; "b'"; "tb'"; "env1'"; ""; ""]
     %> case "next"
     %> exists' ["a"; "ta"; "cons b tb (cons c tc env2)"]
     %> repeat solve
     %> case "next"
     %> exists' ["b"; "tb"; "cons c tc env2"]
     %> repeat solve
     %> case "next"
     %> exists' ["c"; "tc"; "env2"]
     %> repeat solve
     %> apply_assm_spec "H" ["d"; "td"]
     %> apply_assm "Hd"
  |> qed

let env_inclusion_double_skip_thm' =
  lambda_thm
  $ unwords
      [ "forall a :atom. forall ta :term.                        "
      ; "forall b :atom. forall tb :term.                        "
      ; "forall c :atom. forall tc :term.                        "
      ; "forall env1 env2 : term.                                "
      ; " [c # a b] =>                                           "
      ; " (EnvInclusion env1 env2) =>                            "
      ; " (EnvInclusion {cons a ta (cons b tb (cons c tc env1))} "
      ; "               {cons c tc (cons a ta (cons b tb env2))})" ]

let env_inclusion_double_skip' =
  proof' env_inclusion_double_skip_thm'
  |> repeat intro
  |> intros ["H"] %> compute %> intros ["d"; "td"] %> intro'
  |> intros' ["Hda"; "enva"]
     %> case "next"
     %> exists' ["c"; "tc"; "cons a ta (cons b tb env2)"]
     %> repeat solve
     %> case "current"
     %> exists "cons b tb env2"
     %> solve
  |> intros' ["Hnext"; "a'"; "ta'"; "enva'"; ""; ""; ""]
  |> intros' ["Hdb"; "envb"]
     %> case "next"
     %> exists' ["c"; "tc"; "cons a ta (cons b tb env2)"]
     %> repeat solve
     %> case "next"
     %> exists' ["a"; "ta"; "cons d td env2"]
     %> repeat solve
     %> case "current"
     %> exists "env2"
     %> solve
  |> intros' ["Hd"; "b'"; "tb'"; "envb'"; ""; ""; ""]
  |> intros' ["Hdc"; "envc"] %> case "current" %> exists "cons a ta (cons b tb env2)" %> solve
  |> intros' ["Hd"; "c'"; "tc'"; "env1'"; ""; ""]
     %> case "next"
     %> exists' ["c"; "tc"; "cons a ta (cons b tb env2)"]
     %> repeat solve
     %> case "next"
     %> exists' ["a"; "ta"; "cons b tb env2"]
     %> repeat solve
     %> case "next"
     %> exists' ["b"; "tb"; "env2"]
     %> repeat solve
     %> apply_assm_spec "H" ["d"; "td"]
     %> apply_assm "Hd"
  |> qed

let swap_lambda_typing_lemma_thm =
  lambda_thm
  $ unwords
      [ "forall e env t :term.                              "
      ; "forall a :atom. forall ta :term.                   "
      ; "forall b :atom. forall tb :term.                   "
      ; "(Typing {e}       {cons a ta (cons b tb env)} t) =>"
      ; "(Typing {[a b] e} {cons b ta (cons a tb env)} t)" ]

let swap_lambda_typing_lemma =
  proof' swap_lambda_typing_lemma_thm
  |> by_induction "e0" "IH" %> repeat intro %> intro'
  |> intros' ["Hc"; "c"; ""; ""]
     %> intros' ["Hcurr"; "env'"]
     %> case "var"
     %> exists "b"
     %> solve
     %> case "current"
     %> exists "cons a tb env"
     %> solve
     %> intros' ["Hdiff"; "d"; "td"; "env'"; ""; ""; ""]
     %> intros' ["Hcurr"; "env''"]
     %> case "var"
     %> exists "a"
     %> solve
     %> case "next"
     %> exists' ["b"; "ta"; "cons a tb env"]
     %> solve
     %> solve
     %> case "current"
     %> exists "env"
     %> solve
     %> intros' ["Hdiff"; "f"; "tf"; "env''"; ""; ""]
     %> case "var"
     %> exists "c"
     %> solve
     %> case "next"
     %> exists' ["b"; "ta"; "cons a tb env"]
     %> repeat solve
     %> case "next"
     %> exists' ["a"; "tb"; "env''"]
     %> repeat solve
     %> assumption
  |> intros' ["Hlam"; "c"; "e_c"; "t1"; "t2"; ""; ""; ""] %> compare_atoms "c" "a"
  |> intro'
     %> case "lam"
     %> exists' ["b"; "[b a]e_c"; "t1"; "t2"]
     %> solve
     %> solve
     %> destruct_goal
     %> assumption
     %> apply_thm_spec weakening_lemma
          ["[b a]e_c"; "cons b t1 (cons a tb env)"; "t2"; "cons b t1 (cons b ta (cons a tb env))"]
     %> apply_assm_spec "IH" ["e_c"; "env"; "t2"; "a"; "t1"; "b"; "tb"]
     %> solve
     %> apply_thm_spec weakening_lemma
          ["e_c"; "cons c t1 (cons a ta (cons b tb env))"; "t2"; "cons a t1 (cons b tb env)"]
     %> apply_assm "Hlam_2"
     %> apply_thm_spec shadow ["a"; "t1"; "ta"; "cons b tb env"]
     %> apply_thm_spec shadow' ["b"; "t1"; "ta"; "cons a tb env"]
  |> intro' %> compare_atoms "c" "b"
  |> intro'
     %> case "lam"
     %> exists' ["a"; "[a b]e_c"; "t1"; "t2"]
     %> repeat solve
     %> destruct_goal
     %> apply_assm "Hlam_1"
     %> apply_assm_spec "IH" ["e_c"; "cons a tb env"; "t2"; "b"; "t1"; "a"; "ta"]
     %> solve
     %> apply_thm_spec weakening_lemma
          ["e_c"; "cons c t1 (cons a ta (cons b tb env))"; "t2"; "cons b t1 (cons a ta (cons a tb env))"]
     %> apply_assm "Hlam_2"
     %> compute
     %> intros ["d"; "td"]
     %> intro'
     %> intros' ["Hcurr"; "envd"]
     %> case "current"
     %> exists "cons a ta (cons a tb env)"
     %> solve
     %> intros' ["Hnext"; "f"; "tf"; "envf"; ""; ""; ""]
     %> intros' ["Hcurr"; "envd"]
     %> case "next"
     %> exists' ["b"; "t1"; "cons a ta (cons a tb env)"]
     %> repeat solve
     %> case "current"
     %> exists "cons a tb env"
     %> solve
     %> intros' ["Hnext"; "g"; "tg"; "envg"; ""; ""]
     %> case "next"
     %> exists' ["b"; "t1"; "cons a ta (cons a tb env)"]
     %> repeat solve
     %> case "next"
     %> exists' ["a"; "ta"; "cons a tb env"]
     %> solve
     %> solve
     %> destruct_assm "Hnext"
     %> intros' ["contra"; "_env"]
     %> discriminate
     %> intros' ["Hcurr"; "h"; "th"; "envh"; ""; ""]
     %> case "next"
     %> exists' ["a"; "tb"; "envh"]
     %> solve
     %> solve
     %> apply_assm "Hcurr"
  |> intro'
     %> case "lam"
     %> exists' ["c"; "[a b]e_c"; "t1"; "t2"]
     %> repeat solve
     %> destruct_goal
     %> assumption
     %> apply_thm_spec weakening_lemma
          ["[a b]e_c"; "cons b ta (cons a tb (cons c t1 env))"; "t2"; "cons c t1 (cons b ta (cons a tb env))"]
     %> apply_assm_spec "IH" ["e_c"; "cons c t1 env"; "t2"; "a"; "ta"; "b"; "tb"]
     %> solve
     %> apply_thm_spec weakening_lemma
          ["e_c"; "cons c t1 (cons a ta (cons b tb env))"; "t2"; "cons a ta (cons b tb (cons c t1 env))"]
     %> assumption
     %> ( apply_thm_spec env_inclusion_double_skip ["a"; "ta"; "b"; "tb"; "c"; "t1"; "env"; "env"]
        %> solve
        %> apply_thm_spec env_inclusion_refl ["env"] )
     %> ( apply_thm_spec env_inclusion_double_skip' ["b"; "ta"; "a"; "tb"; "c"; "t1"; "env"; "env"]
        %> solve
        %> apply_thm_spec env_inclusion_refl ["env"] )
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["[a b]e1"; "[a b]e2"; "t2"]
     %> solve
     %> destruct_goal
     %> apply_assm_spec "IH" ["e1"; "env"; "arrow t2 t"; "a"; "ta"; "b"; "tb"]
     %> solve
     %> apply_assm "Happ_1"
     %> apply_assm_spec "IH" ["e2"; "env"; "t2"; "a"; "ta"; "b"; "tb"]
     %> solve
     %> apply_assm "Happ_2"
  |> qed

let swap_lambda_typing'_thm =
  lambda_thm
  $ unwords
      [ "forall e env t :term. "
      ; "forall a b :atom. forall t' :term. "
      ; " [b # e] => "
      ; " (Typing {e} {cons a t' env} t) => "
      ; " (Typing {[a b]e} {cons b t' env} t)" ]

let swap_lambda_typing' =
  proof' swap_lambda_typing'_thm
  |> by_induction "e0" "IH" %> repeat intro
  |> compare_atoms "a" "b" %> intro' %> trivial %> intro'
  |> intro'
  |> intros' ["Hc"; "c"; ""; ""]
     %> intros' ["Heq"; "env'"]
     %> case "var"
     %> exists "b"
     %> solve
     %> case "current"
     %> exists "env"
     %> solve
     %> intros' ["Hdiff"; "d"; "td"; "env'"; ""; ""]
     %> case "var"
     %> exists "c"
     %> solve
     %> case "next"
     %> exists' ["b"; "t'"; "env'"]
     %> solve
     %> solve
     %> apply_assm "Hdiff"
  |> intros' ["Hlam"; "c"; "e_c"; "t1"; "t2"; ""; ""; ""] %> compare_atoms "a" "c"
  |> intro'
     %> case "lam"
     %> exists' ["b"; "[a b]e_c"; "t1"; "t2"]
     %> solve
     %> solve
     %> destruct_goal
     %> assumption
     %> apply_thm_spec weakening_lemma ["[a b]e_c"; "cons b t1 env"; "t2"; "cons b t1 (cons b t' env)"]
     %> apply_assm_spec "IH" ["e_c"; "env"; "t2"; "a"; "b"; "t1"]
     %> solve
     %> solve
     %> apply_thm_spec weakening_lemma ["e_c"; "cons c t1 (cons a t' env)"; "t2"; "cons a t1 env"]
     %> assumption
     %> apply_thm_spec shadow ["a"; "t1"; "t'"; "env"]
     %> apply_thm_spec shadow' ["b"; "t1"; "t'"; "env"]
  |> intro' %> compare_atoms "b" "c" %> intro'
  |> case "lam" %> exists' ["a"; "[a b]e_c"; "t1"; "t2"] %> repeat solve %> destruct_goal %> assumption
  |> apply_thm_spec swap_lambda_typing_lemma ["e_c"; "env"; "t2"; "c"; "t1"; "a"; "t'"] %> assumption
  |> intro' %> case "lam" %> exists' ["c"; "[a b]e_c"; "t1"; "t2"] %> repeat solve %> destruct_goal %> assumption
  |> apply_thm_spec weakening_lemma ["[a b]e_c"; "cons b t' (cons c t1 env)"; "t2"; "cons c t1 (cons b t' env)"]
  |> apply_assm_spec "IH" ["e_c"; "cons c t1 env"; "t2"; "a"; "b"; "t'"] %> repeat solve
  |> apply_thm_spec weakening_lemma ["e_c"; "cons c t1 (cons a t' env)"; "t2"; "cons a t' (cons c t1 env)"]
     %> apply_assm "Hlam_2"
  |> apply_thm_spec env_inclusion_shuffle ["c"; "t1"; "a"; "t'"; "env"] %> solve
  |> apply_thm_spec env_inclusion_shuffle ["b"; "t'"; "c"; "t1"; "env"] %> solve
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["[a b]e1"; "[a b]e2"; "t2"]
     %> solve
     %> destruct_goal
     %> apply_assm_spec "IH" ["e1"; "env"; "arrow t2 t"; "a"; "b"; "t'"]
     %> repeat solve
     %> apply_assm "Happ_1"
     %> apply_assm_spec "IH" ["e2"; "env"; "t2"; "a"; "b"; "t'"]
     %> repeat solve
     %> apply_assm "Happ_2"
  |> qed

let swap_lambda_typing_thm =
  lambda_thm
  $ unwords
      [ "forall a :atom. forall e_a :term.   "
      ; "forall b :atom. forall e_b :term.   "
      ; "forall env t1 t2 :term.             "
      ; "  [a.e_a = b.e_b] =>                "
      ; "  (Typing e_a {cons a t1 env} t2) =>"
      ; "  (Typing e_b {cons b t1 env} t2)" ]

let swap_lambda_typing =
  proof' swap_lambda_typing_thm
  |> repeat intro %> intros ["Ha"] %> compare_atoms "a" "b"
  |> intro' %> trivial
  |> intro' %> apply_thm_spec swap_lambda_typing' ["e_a"; "env"; "t2"; "a"; "b"; "t1"] %> solve %> assumption
  |> qed

let typing_cons_fresh_thm =
  lambda_thm
  $ unwords
      [ "forall e t env : term."
      ; "forall a : atom. forall ta : term."
      ; " [a # e] => "
      ; " (Typing e env t) => "
      ; " (Typing e {cons a ta env} t)" ]

let typing_cons_fresh =
  proof' typing_cons_fresh_thm
  |> by_induction "e0" "IH"
  |> intros ["t"; "env"; "a"; "ta"]
  |> intro
  |> intros' ["Ht"; ""]
  |> intros' ["Hb"; "b"; ""]
     %> case "var"
     %> exists "b"
     %> solve
     %> case "next"
     %> exists' ["a"; "ta"; "env"]
     %> solve
     %> solve
     %> assumption
  |> intros' ["Hlam"; "b"; "e_b"; "t1"; "t2"; ""; ""; ""]
     %> get_fresh_atom "c" "a b e_b t1 t2 env"
     %> case "lam"
     %> exists' ["c"; "[c b]e_b"; "t1"; "t2"]
     %> repeat solve
     %> destruct_goal
     %> assumption
     %> apply_thm_spec weakening_lemma ["[c b]e_b"; "cons a ta (cons c t1 env)"; "t2"; "cons c t1 (cons a ta env)"]
     %> apply_assm_spec "IH" ["[c b]e_b"; "t2"; "cons c t1 env"; "a"; "ta"]
     %> repeat solve
     %> apply_thm_spec swap_lambda_typing' ["e_b"; "env"; "t2"; "b"; "c"; "t1"]
     %> solve
     %> apply_assm "Hlam_2"
     %> apply_thm_spec env_inclusion_shuffle ["a"; "ta"; "c"; "t1"; "env"]
     %> solve
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["e1"; "e2"; "t2"]
     %> solve
     %> destruct_goal
     %> apply_assm_spec "IH" ["e1"; "arrow t2 t"; "env"; "a"; "ta"]
     %> repeat solve
     %> apply_assm "Happ_1"
     %> apply_assm_spec "IH" ["e2"; "t2"; "env"; "a"; "ta"]
     %> repeat solve
     %> apply_assm "Happ_2"
  |> qed

let empty_contradiction_thm = lambda_thm "forall a :atom. forall t :term. (InEnv nil a t) => false"

let empty_contradiction =
  proof' empty_contradiction_thm
  |> intro %> intro %> intros ["H"] %> destruct_assm "H"
  |> intros' ["contra"; "env'"] %> solve
  |> intros' ["contra"; "b"; "s"; "env'"; ""] %> solve
  |> qed
