open Nominal.Prelude
open Nominal.Prover
open Nominal.Tactics
open Nominal.Printing
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
  |> intros' ["Hcurrent"; "env3"] %> case "current" %> exists "env2" %> by_solver
  |> intros' ["Hnext"; "c"; "tc"; "env3"; ""; ""]
     %> case "next"
     %> exists' ["c"; "tc"; "env2"]
     %> by_solver
     %> by_solver
     %> apply_assm_specialized "Hinclusion" ["a"; "t"]
     %> apply_assm "Hnext"
  |> qed

let weakening_lemma_thm =
  lambda_thm "forall e env1 t env2 : term. (Typing e env1 t) => (EnvInclusion env1 env2) => (Typing e env2 t)"

let weakening_lemma =
  proof' weakening_lemma_thm
  |> by_induction "e0" "IH"
  |> repeat intro
  |> intros ["Htyp"; "Hinc"] %> destruct_assm "Htyp"
  |> intros' ["Hb"; "b"; ""]
     %> case "var"
     %> exists "b"
     %> by_solver
     %> apply_assm_specialized "Hinc" ["b"; "t"]
     %> assumption
  |> intros' ["Hlam"; "b"; "e_b"; "t1"; "t2"; ""; ""; ""]
     %> case "lam"
     %> exists' ["b"; "e_b"; "t1"; "t2"]
     %> by_solver
     %> by_solver
     %> destruct_goal
     %> assumption
     %> apply_assm_specialized "IH" ["e_b"; "cons b t1 env1"; "t2"; "cons b t1 env2"]
     %> by_solver
     %> assumption
     %> apply_thm_specialized env_inclusion_cons_both ["env1"; "env2"; "b"; "t1"]
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["e1"; "e2"; "t2"]
     %> by_solver
     %> destruct_goal
     %> apply_assm_specialized "IH" ["e1"; "env1"; "arrow t2 t"; "env2"]
     %> by_solver
     %> assumption
     %> assumption
     %> apply_assm_specialized "IH" ["e2"; "env1"; "t2"; "env2"]
     %> by_solver
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
  |> compute %> intros ["b"; "tb"] %> destr_intro
  |> intros' ["Hcurrent"; "env'"; ""] %> case "current" %> exists "env" %> by_solver
  |> intros' ["Hnext"; "c"; "tc"; "envc"; ""; ""; ""]
  |> intros' ["contra"; "envc'"] %> discriminate
  |> intros' ["Hnext"; "d"; "td"; "envd"; ""; ""]
     %> case "next"
     %> exists' ["a"; "t1"; "env"]
     %> by_solver
     %> by_solver
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
  |> repeat intro %> compute %> intros ["b"; "tb"] %> destr_intro
  |> intros' ["Hcurrent"; "env'"; ""] %> case "current" %> exists "(cons a t2 env)" %> by_solver
  |> intros' ["Hnext"; "c"; "tc"; "envc"; ""; ""]
     %> case "next"
     %> exists' ["a"; "t1"; "cons a t2 envc"]
     %> by_solver
     %> by_solver
     %> case "next"
     %> exists' ["a"; "t2"; "envc"]
     %> by_solver
     %> by_solver
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
  |> repeat intro %> compute %> intros ["c"; "tc"] %> destr_intro
  |> intros' ["Hcurrent"; "envc"; ""]
     %> case "next"
     %> exists' ["b"; "tb"; "cons a ta env"]
     %> by_solver
     %> by_solver
     %> case "current"
     %> exists "env"
     %> by_solver
  |> intros' ["Hnext"; "d"; "td"; "envd"; ""; ""; ""]
  |> intros' ["H"; "envc"; ""] %> case "current" %> exists "cons a ta env" %> by_solver
  |> intros' ["H"; "e"; "te"; "enve"; ""; ""]
     %> case "next"
     %> exists' ["b"; "tb"; "cons a ta env"]
     %> by_solver
     %> by_solver
     %> case "next"
     %> exists' ["a"; "ta"; "enve"]
     %> by_solver
     %> by_solver
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
     %> apply_thm_specialized weakening_lemma ["e"; "cons a ta (cons b tb env)"; "t"; "cons b tb (cons a ta env)"]
     %> apply_assm "H"
     %> apply_thm_specialized env_inclusion_shuffle ["a"; "ta"; "b"; "tb"; "env"]
     %> by_solver
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
  |> by_induction "e0" "IH" %> repeat intro %> destr_intro
  |> intros' ["Hb"; "b"; ""]
     %> case "var"
     %> exists "b"
     %> by_solver
     %> case "next"
     %> exists' ["a"; "ta"; "env"]
     %> by_solver
     %> by_solver
     %> apply_assm "Hb"
  |> intros' ["Hlam"; "b"; "e_b"; "t1"; "t2"; ""; ""; ""]
     %> case "lam"
     %> compare_atoms "a" "b"
     %> destr_intro
     %> exists' ["b"; "e_b"; "t1"; "t2"]
     %> by_solver
     %> by_solver
     %> destruct_goal
     %> apply_assm "Hlam_1"
     %> apply_thm_specialized weakening_lemma ["e_b"; "cons b t1 env"; "t2"; "cons b t1 (cons a ta env)"]
     %> apply_assm "Hlam_2"
     %> apply_thm_specialized shadow' ["b"; "t1"; "ta"; "env"]
     %> destr_intro
     %> exists' ["b"; "e_b"; "t1"; "t2"]
     %> by_solver
     %> by_solver
     %> destruct_goal
     %> apply_assm "Hlam_1"
     %> apply_thm_specialized weakening_lemma ["e_b"; "cons a ta (cons b t1 env)"; "t2"; "cons b t1 (cons a ta env)"]
     %> apply_assm_specialized "IH" ["e_b"; "cons b t1 env"; "t2"; "a"; "ta"]
     %> by_solver
     %> by_solver
     %> apply_assm "Hlam_2"
     %> apply_thm_specialized env_inclusion_shuffle ["a"; "ta"; "b"; "t1"; "env"]
     %> by_solver
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["e1"; "e2"; "t2"]
     %> by_solver
     %> destruct_goal
     %> apply_assm_specialized "IH" ["e1"; "env"; "arrow t2 t"; "a"; "ta"]
     %> by_solver
     %> by_solver
     %> apply_assm "Happ_1"
     %> apply_assm_specialized "IH" ["e2"; "env"; "t2"; "a"; "ta"]
     %> by_solver
     %> by_solver
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
  |> intros ["a"; "b"; "c"] %> by_induction "e0" "IH" %> intro %> intro %> destr_intro
  |> intros' ["Hcurrent"; "env'"; ""] %> case "current" %> exists "[a b]env'" %> by_solver
  |> intros' ["Hnext"; "d"; "td"; "env'"; ""; ""]
     %> case "next"
     %> exists' ["[a b]d"; "[a b]td"; "[a b]env'"]
     %> by_solver
     %> by_solver
     %> apply_assm_specialized "IH" ["env'"; "t"]
     %> by_solver
     %> by_solver
     %> assumption
  |> qed

let atom_fresh_in_type_thm = lambda_thm "forall a : atom. forall t: term. (Type t) => (a # t)"

let atom_fresh_in_type =
  proof' atom_fresh_in_type_thm
  |> intros ["a"]
     %> by_induction "t0" "IH"
     %> destr_intro
     %> intros ["Hbase"]
     %> by_solver
     %> intros' ["Harrow"; "t1"; "t2"; ""; ""]
     %> add_assumption_parse "Ht1" "a # t1"
     %> add_assumption_parse "Ht2" "a # t2"
     %> by_solver
     %> apply_assm_specialized "IH" ["t2"]
     %> by_solver
     %> assumption
     %> apply_assm_specialized "IH" ["t1"]
     %> by_solver
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
  |> intros ["H"] %> compute %> intros ["d"; "td"] %> destr_intro
  |> intros' ["Hdc"; "envc"]
     %> case "next"
     %> exists' ["a"; "ta"; "cons b tb (cons c tc env2)"]
     %> repeat by_solver
     %> case "next"
     %> exists' ["b"; "tb"; "cons c tc env2"]
     %> repeat by_solver
     %> case "current"
     %> exists "env2"
     %> by_solver
  |> intros' ["Hnext"; "c'"; "tc'"; "envc'"; ""; ""; ""]
  |> intros' ["Hda"; "enva"] %> case "current" %> exists "cons b tb (cons c tc env2)" %> by_solver
  |> intros' ["Hnext"; "a'"; "ta'"; "enva'"; ""; ""; ""]
  |> intros' ["Hdb"; "envb"]
     %> case "next"
     %> exists' ["a"; "ta"; "cons b tb (cons c tc env2)"]
     %> repeat by_solver
     %> case "current"
     %> exists "cons c tc env2"
     %> by_solver
  |> intros' ["Hd"; "b'"; "tb'"; "env1'"; ""; ""]
     %> case "next"
     %> exists' ["a"; "ta"; "cons b tb (cons c tc env2)"]
     %> repeat by_solver
     %> case "next"
     %> exists' ["b"; "tb"; "cons c tc env2"]
     %> repeat by_solver
     %> case "next"
     %> exists' ["c"; "tc"; "env2"]
     %> repeat by_solver
     %> apply_assm_specialized "H" ["d"; "td"]
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
  |> intros ["H"] %> compute %> intros ["d"; "td"] %> destr_intro
  |> intros' ["Hda"; "enva"]
     %> case "next"
     %> exists' ["c"; "tc"; "cons a ta (cons b tb env2)"]
     %> repeat by_solver
     %> case "current"
     %> exists "cons b tb env2"
     %> by_solver
  |> intros' ["Hnext"; "a'"; "ta'"; "enva'"; ""; ""; ""]
  |> intros' ["Hdb"; "envb"]
     %> case "next"
     %> exists' ["c"; "tc"; "cons a ta (cons b tb env2)"]
     %> repeat by_solver
     %> case "next"
     %> exists' ["a"; "ta"; "cons d td env2"]
     %> repeat by_solver
     %> case "current"
     %> exists "env2"
     %> by_solver
  |> intros' ["Hd"; "b'"; "tb'"; "envb'"; ""; ""; ""]
  |> intros' ["Hdc"; "envc"] %> case "current" %> exists "cons a ta (cons b tb env2)" %> by_solver
  |> intros' ["Hd"; "c'"; "tc'"; "env1'"; ""; ""]
     %> case "next"
     %> exists' ["c"; "tc"; "cons a ta (cons b tb env2)"]
     %> repeat by_solver
     %> case "next"
     %> exists' ["a"; "ta"; "cons b tb env2"]
     %> repeat by_solver
     %> case "next"
     %> exists' ["b"; "tb"; "env2"]
     %> repeat by_solver
     %> apply_assm_specialized "H" ["d"; "td"]
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
  |> by_induction "e0" "IH" %> repeat intro %> destr_intro
  |> intros' ["Hc"; "c"; ""; ""]
     %> intros' ["Hcurr"; "env'"]
     %> case "var"
     %> exists "b"
     %> by_solver
     %> case "current"
     %> exists "cons a tb env"
     %> by_solver
     %> intros' ["Hdiff"; "d"; "td"; "env'"; ""; ""; ""]
     %> intros' ["Hcurr"; "env''"]
     %> case "var"
     %> exists "a"
     %> by_solver
     %> case "next"
     %> exists' ["b"; "ta"; "cons a tb env"]
     %> by_solver
     %> by_solver
     %> case "current"
     %> exists "env"
     %> by_solver
     %> intros' ["Hdiff"; "f"; "tf"; "env''"; ""; ""]
     %> case "var"
     %> exists "c"
     %> by_solver
     %> case "next"
     %> exists' ["b"; "ta"; "cons a tb env"]
     %> repeat by_solver
     %> case "next"
     %> exists' ["a"; "tb"; "env''"]
     %> repeat by_solver
     %> assumption
  |> intros' ["Hlam"; "c"; "e_c"; "t1"; "t2"; ""; ""; ""] %> compare_atoms "c" "a"
  |> destr_intro
     %> case "lam"
     %> exists' ["b"; "[b a]e_c"; "t1"; "t2"]
     %> by_solver
     %> by_solver
     %> destruct_goal
     %> assumption
     %> apply_thm_specialized weakening_lemma
          ["[b a]e_c"; "cons b t1 (cons a tb env)"; "t2"; "cons b t1 (cons b ta (cons a tb env))"]
     %> apply_assm_specialized "IH" ["e_c"; "env"; "t2"; "a"; "t1"; "b"; "tb"]
     %> by_solver
     %> apply_thm_specialized weakening_lemma
          ["e_c"; "cons c t1 (cons a ta (cons b tb env))"; "t2"; "cons a t1 (cons b tb env)"]
     %> apply_assm "Hlam_2"
     %> apply_thm_specialized shadow ["a"; "t1"; "ta"; "cons b tb env"]
     %> apply_thm_specialized shadow' ["b"; "t1"; "ta"; "cons a tb env"]
  |> destr_intro %> compare_atoms "c" "b"
  |> destr_intro
     %> case "lam"
     %> exists' ["a"; "[a b]e_c"; "t1"; "t2"]
     %> repeat by_solver
     %> destruct_goal
     %> apply_assm "Hlam_1"
     %> apply_assm_specialized "IH" ["e_c"; "cons a tb env"; "t2"; "b"; "t1"; "a"; "ta"]
     %> by_solver
     %> apply_thm_specialized weakening_lemma
          ["e_c"; "cons c t1 (cons a ta (cons b tb env))"; "t2"; "cons b t1 (cons a ta (cons a tb env))"]
     %> apply_assm "Hlam_2"
     %> compute
     %> intros ["d"; "td"]
     %> destr_intro
     %> intros' ["Hcurr"; "envd"]
     %> case "current"
     %> exists "cons a ta (cons a tb env)"
     %> by_solver
     %> intros' ["Hnext"; "f"; "tf"; "envf"; ""; ""; ""]
     %> intros' ["Hcurr"; "envd"]
     %> case "next"
     %> exists' ["b"; "t1"; "cons a ta (cons a tb env)"]
     %> repeat by_solver
     %> case "current"
     %> exists "cons a tb env"
     %> by_solver
     %> intros' ["Hnext"; "g"; "tg"; "envg"; ""; ""]
     %> case "next"
     %> exists' ["b"; "t1"; "cons a ta (cons a tb env)"]
     %> repeat by_solver
     %> case "next"
     %> exists' ["a"; "ta"; "cons a tb env"]
     %> by_solver
     %> by_solver
     %> destruct_assm "Hnext"
     %> intros' ["contra"; "_env"]
     %> discriminate
     %> intros' ["Hcurr"; "h"; "th"; "envh"; ""; ""]
     %> case "next"
     %> exists' ["a"; "tb"; "envh"]
     %> by_solver
     %> by_solver
     %> apply_assm "Hcurr"
  |> destr_intro
     %> case "lam"
     %> exists' ["c"; "[a b]e_c"; "t1"; "t2"]
     %> repeat by_solver
     %> destruct_goal
     %> assumption
     %> apply_thm_specialized weakening_lemma
          ["[a b]e_c"; "cons b ta (cons a tb (cons c t1 env))"; "t2"; "cons c t1 (cons b ta (cons a tb env))"]
     %> apply_assm_specialized "IH" ["e_c"; "cons c t1 env"; "t2"; "a"; "ta"; "b"; "tb"]
     %> by_solver
     %> apply_thm_specialized weakening_lemma
          ["e_c"; "cons c t1 (cons a ta (cons b tb env))"; "t2"; "cons a ta (cons b tb (cons c t1 env))"]
     %> assumption
     %> ( apply_thm_specialized env_inclusion_double_skip ["a"; "ta"; "b"; "tb"; "c"; "t1"; "env"; "env"]
        %> by_solver
        %> apply_thm_specialized env_inclusion_refl ["env"] )
     %> ( apply_thm_specialized env_inclusion_double_skip' ["b"; "ta"; "a"; "tb"; "c"; "t1"; "env"; "env"]
        %> by_solver
        %> apply_thm_specialized env_inclusion_refl ["env"] )
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["[a b]e1"; "[a b]e2"; "t2"]
     %> by_solver
     %> destruct_goal
     %> apply_assm_specialized "IH" ["e1"; "env"; "arrow t2 t"; "a"; "ta"; "b"; "tb"]
     %> by_solver
     %> apply_assm "Happ_1"
     %> apply_assm_specialized "IH" ["e2"; "env"; "t2"; "a"; "ta"; "b"; "tb"]
     %> by_solver
     %> apply_assm "Happ_2"
  |> qed

let swap_lambda_typing_thm =
  lambda_thm
  $ unwords
      [ "forall e env t :term. "
      ; "forall a b :atom. forall t' :term. "
      ; " [b # a e] => "
      ; " (Typing {e} {cons a t' env} t) => "
      ; " (Typing {[a b]e} {cons b t' env} t)" ]

let swap_lambda_typing =
  proof' swap_lambda_typing_thm
  |> by_induction "e0" "IH" %> repeat intro %> destr_intro
  |> intros' ["Hc"; "c"; ""; ""]
     %> intros' ["Heq"; "env'"]
     %> case "var"
     %> exists "b"
     %> by_solver
     %> case "current"
     %> exists "env"
     %> by_solver
     %> intros' ["Hdiff"; "d"; "td"; "env'"; ""; ""]
     %> case "var"
     %> exists "c"
     %> by_solver
     %> case "next"
     %> exists' ["b"; "t'"; "env'"]
     %> by_solver
     %> by_solver
     %> apply_assm "Hdiff"
  |> intros' ["Hlam"; "c"; "e_c"; "t1"; "t2"; ""; ""; ""] %> compare_atoms "a" "c"
  |> destr_intro
     %> case "lam"
     %> exists' ["b"; "[a b]e_c"; "t1"; "t2"]
     %> by_solver
     %> by_solver
     %> destruct_goal
     %> assumption
     %> apply_thm_specialized weakening_lemma ["[a b]e_c"; "cons b t1 env"; "t2"; "cons b t1 (cons b t' env)"]
     %> apply_assm_specialized "IH" ["e_c"; "env"; "t2"; "a"; "b"; "t1"]
     %> by_solver
     %> by_solver
     %> apply_thm_specialized weakening_lemma ["e_c"; "cons c t1 (cons a t' env)"; "t2"; "cons a t1 env"]
     %> assumption
     %> apply_thm_specialized shadow ["a"; "t1"; "t'"; "env"]
     %> apply_thm_specialized shadow' ["b"; "t1"; "t'"; "env"]
  |> destr_intro %> compare_atoms "b" "c" %> destr_intro
  |> case "lam" %> exists' ["a"; "[a b]e_c"; "t1"; "t2"] %> repeat by_solver %> destruct_goal %> assumption
  |> apply_thm_specialized swap_lambda_typing_lemma ["e_c"; "env"; "t2"; "c"; "t1"; "a"; "t'"] %> assumption
  |> destr_intro
     %> case "lam"
     %> exists' ["c"; "[a b]e_c"; "t1"; "t2"]
     %> repeat by_solver
     %> destruct_goal
     %> assumption
  |> apply_thm_specialized weakening_lemma ["[a b]e_c"; "cons b t' (cons c t1 env)"; "t2"; "cons c t1 (cons b t' env)"]
  |> apply_assm_specialized "IH" ["e_c"; "cons c t1 env"; "t2"; "a"; "b"; "t'"] %> repeat by_solver
  |> apply_thm_specialized weakening_lemma ["e_c"; "cons c t1 (cons a t' env)"; "t2"; "cons a t' (cons c t1 env)"]
     %> apply_assm "Hlam_2"
  |> apply_thm_specialized env_inclusion_shuffle ["c"; "t1"; "a"; "t'"; "env"] %> by_solver
  |> apply_thm_specialized env_inclusion_shuffle ["b"; "t'"; "c"; "t1"; "env"] %> by_solver
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["[a b]e1"; "[a b]e2"; "t2"]
     %> by_solver
     %> destruct_goal
     %> apply_assm_specialized "IH" ["e1"; "env"; "arrow t2 t"; "a"; "b"; "t'"]
     %> repeat by_solver
     %> apply_assm "Happ_1"
     %> apply_assm_specialized "IH" ["e2"; "env"; "t2"; "a"; "b"; "t'"]
     %> repeat by_solver
     %> apply_assm "Happ_2"
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
     %> by_solver
     %> case "next"
     %> exists' ["a"; "ta"; "env"]
     %> by_solver
     %> by_solver
     %> assumption
  |> intros' ["Hlam"; "b"; "e_b"; "t1"; "t2"; ""; ""; ""]
     %> get_fresh_atom "c" "a b e_b t1 t2 env"
     %> case "lam"
     %> exists' ["c"; "[c b]e_b"; "t1"; "t2"]
     %> repeat by_solver
     %> destruct_goal
     %> assumption
     %> apply_thm_specialized weakening_lemma
          ["[c b]e_b"; "cons a ta (cons c t1 env)"; "t2"; "cons c t1 (cons a ta env)"]
     %> apply_assm_specialized "IH" ["[c b]e_b"; "t2"; "cons c t1 env"; "a"; "ta"]
     %> repeat by_solver
     %> apply_thm_specialized swap_lambda_typing ["e_b"; "env"; "t2"; "b"; "c"; "t1"]
     %> by_solver
     %> apply_assm "Hlam_2"
     %> apply_thm_specialized env_inclusion_shuffle ["a"; "ta"; "c"; "t1"; "env"]
     %> by_solver
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app"
     %> exists' ["e1"; "e2"; "t2"]
     %> by_solver
     %> destruct_goal
     %> apply_assm_specialized "IH" ["e1"; "arrow t2 t"; "env"; "a"; "ta"]
     %> repeat by_solver
     %> apply_assm "Happ_1"
     %> apply_assm_specialized "IH" ["e2"; "t2"; "env"; "a"; "ta"]
     %> repeat by_solver
     %> apply_assm "Happ_2"
  |> qed

let empty_contradiction_thm = lambda_thm "forall a :atom. forall t :term. (InEnv nil a t) => false"

let empty_contradiction =
  proof' empty_contradiction_thm
  |> intro %> intro %> intros ["H"] %> destruct_assm "H"
  |> intros' ["contra"; "env'"] %> by_solver
  |> intros' ["contra"; "b"; "s"; "env'"; ""] %> by_solver
  |> qed
