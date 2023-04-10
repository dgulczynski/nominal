open Nominal.Common
open Nominal.Parser
open Nominal.Proof
open Nominal.ProofEnv
open Nominal.Prover
open Nominal.Tactics
open Nominal.Printing

let type_formula =
  unwords
    [ "fix Type(t): * =                                                            "
    ; "  base: t = base                                                            "
    ; "  ∨                                                                         "
    ; "  arrow: ( exists t1 t2 :term. [t = arrow t1 t2] ∧ (Type t1) ∧ (Type t2) )" ]

let inenv_formula =
  unwords
    [ "fix InEnv(env): forall a :atom. forall t :term. * = fun a :atom -> fun t :term ->           "
    ; "  current: ( exists env': term. [env = cons a t env'] )                                     "
    ; "  ∨                                                                                         "
    ; "  next: ( exists b :atom. exists s env': term. [env = cons b s env'] ∧ [a =/= b] ∧ (InEnv env' a {t}))"
    ]

let typing_formula =
  unwords
    [ "fix Typing(e): forall env t :term. * = fun env :term -> fun t :term ->                     "
    ; "  var: ( exists a :atom.                                                                   "
    ; "    [e = a] ∧ InEnv {env} a {t} )                                                          "
    ; "  ∨                                                                                        "
    ; "  lam: ( exists a :atom. exists e' t1 t2 :term.                                            "
    ; "    [e = lam (a.e')] ∧ [t = arrow t1 t2] ∧ (Type t1) ∧ (Typing {e'} {cons a t1 env} {t2}) )"
    ; "  ∨                                                                                        "
    ; "  app: ( exists e1 e2 t2 :term.                                                            "
    ; "    [e = app e1 e2] ∧ (Typing {e1} {env} {arrow t2 t}) ∧ (Typing {e2} {env} {t2})       )" ]

let lambda_symbols = funcs_env ["lam"; "app"; "base"; "arrow"; "nil"; "cons"]

let arrow_base_base_is_a_type_thm =
  let env = parse_mapping lambda_symbols [] [] snd [("Type", type_formula)] in
  (env, parse_formula env "Type {arrow base base}")

let arrow_base_base_is_a_type =
  proof' arrow_base_base_is_a_type_thm
  |> compute %> case "arrow"
     %> (exists "base" %> exists "base" %> by_solver)
     %> destruct_goal
     %> repeat (compute %> case "base" %> by_solver)
  |> qed

let var_in_env_types_thm =
  let ids = lambda_symbols @ atoms_env ["c"; "d"] in
  let env = parse_mapping ids [] [] snd [("InEnv", inenv_formula)] in
  (env, parse_formula env "[c =/= d] => InEnv {cons c (arrow base base) (cons d base nil)} d {base}")

let var_in_env_types =
  proof' var_in_env_types_thm
  |> intro %> case "next" %> exists' ["c"; "arrow base base"; "cons d base nil"] %> repeat by_solver
  |> case "current" %> exists "nil" %> by_solver
  |> qed

let app_lam_var_types_thm =
  let ids = lambda_symbols @ atoms_env ["a"; "b"; "c"; "d"] in
  let env =
    parse_mapping ids [] [] snd [("Type", type_formula); ("InEnv", inenv_formula); ("Typing", typing_formula)]
  in
  (env, parse_formula env "Typing {app (lam (c.c)) d} {cons d base nil} {base}")

let app_lam_var_types =
  proof' app_lam_var_types_thm |> case "app"
  |> exists' ["lam (c.c)"; "d"; "base"] %> by_solver
  |> destruct_goal
  |> case "lam"
     %> exists' ["c"; "c"; "base"; "base"]
     %> by_solver %> by_solver %> destruct_goal %> case "base" %> by_solver %> case "var" %> exists "c"
     %> by_solver %> case "current" %> exists "cons d base nil" %> by_solver
  |> case "var" %> exists "d" %> by_solver %> case "current" %> exists "nil" %> by_solver
  |> qed

let term_formula =
  unwords
    [ "fix Term(e): * = "
    ; " var: ( exists a :atom. [e = a] ) "
    ; " ∨ "
    ; " lam: (    exists a :atom. exists e' :term. [e = lam (a.e')] ∧ (Term e') )"
    ; " ∨ "
    ; " app: ( exists e1 e2 :term. [e    = app e1 e2] ∧ (Term e1) ∧ (Term e2) )" ]

let value_formula =
  unwords
    [ "fun e:term -> "
    ; " var: (exists a :atom. [e = a])"
    ; " ∨"
    ; " lam: (exists    a :atom. exists e' : term. [e = lam (a.e')] ∧ (Term e'))" ]

let subst_formula =
  String.concat ""
    [ "fix Sub(e): forall a :atom. forall v e':term.* = fun a :atom ->      fun v :term -> fun e' :term -> "
    ; " var_same: ([e = a] ∧ [e' = v])"
    ; " ∨"
    ; " var_diff: (exists b :atom.      [e = b] ∧ [e' = b] ∧ [a =/= b])"
    ; " ∨"
    ; " lam: (exists b :atom. exists e_b e_b' :term."
    ; " [e = lam      (b.e_b)] ∧ [e' = lam (b.e_b')] ∧ [b # v] ∧ [a =/= b] ∧ (Sub e_b a v e_b'))"
    ; " ∨"
    ; " app: (exists e1 e2      e1' e2' :term."
    ; " [e = app e1 e2] ∧ [e' = app e1' e2'] ∧ (Sub e1 a v e1') ∧ (Sub e2 a v e2'))" ]

let step_formula =
  String.concat ""
    [ "fix Steps(e): forall e' :term.* = fun e' :term -> "
    ; " app_l: (        exists e1 e1' e2 :term. "
    ; " [e = app e1 e2] ∧ [e' = app e1' e2] ∧ (Steps e1 e1')) "
    ; " ∨ "
    ; " app_r: (          exists v e2 e2' :term. "
    ; " [e = app v e2] ∧ [e' = app v e2'] ∧ (Value v) ∧ (Steps e2 e2'))"
    ; " ∨ "
    ; "          app: ( exists a :atom. exists e_a v :term. "
    ; " [e = app (lam (a.e_a)) v] ∧ (Value v) ∧ (Sub e_a a v e'))" ]

let progressive_formula = "fun e:term -> value: (Value e) ∨ steps: (exists e':term. Steps e e')"

let lambda_env =
  parse_mapping lambda_symbols [] [] snd
    [ ("Type", type_formula)
    ; ("InEnv", inenv_formula)
    ; ("Typing", typing_formula)
    ; ("Term", term_formula)
    ; ("Value", value_formula)
    ; ("Sub", subst_formula)
    ; ("Steps", step_formula)
    ; ("Progressive", progressive_formula) ]

let lambda_thm thm = (lambda_env, parse_formula lambda_env thm)

let empty_contradiction_thm = lambda_thm "forall a :atom. forall t :term. (InEnv nil a t) => false"

let empty_contradiction =
  proof' empty_contradiction_thm
  |> intro %> intro %> intros ["H"] %> destruct_assm "H"
  |> intros' ["contra"; "env'"] %> by_solver (* nil = cons a t env' *)
  |> intros' ["contra"; "b"; "s"; "env'"; ""] %> by_solver (* nil = cons env' b s *)
  |> qed

let values_are_terms_thm = lambda_thm "forall v : term. (Value v) => (Term v)"

let values_are_terms =
  proof' values_are_terms_thm |> intro
  |> intros' ["H"; ""]
  |> intros' ["Ha"; "a"] %> case "var" %> exists "a" %> by_solver
  |> intros' ["Hlam"; "a"; "e"; ""] %> case "lam" %> exists "a" %> exists "e" %> by_solver %> assumption
  |> qed

let typing_terms_thm = lambda_thm "forall e env t : term. (Typing e env t) => (Term e)"

let typing_terms =
  proof' typing_terms_thm |> by_induction "e0" "IH" |> intro %> intro
  |> intros' ["He"; ""]
  |> intros' ["Ha"; "a"; ""] %> case "var" %> exists "a" %> by_solver
  |> intros' ["Hlam"; "a"; "e_a"; "t1"; "t2"; ""; ""; ""]
     %> case "lam" %> exists "a" %> exists "e_a" %> by_solver
     %> apply_assm_specialized "IH" ["e_a"; "cons a t1 env"; "t2"]
     %> by_solver %> assumption
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
     %> case "app" %> exists "e1" %> exists "e2" %> by_solver %> destruct_goal
  |> apply_assm_specialized "IH" ["e1"; "env"; "arrow t2 t"] %> by_solver %> apply_assm "Happ_1"
  |> apply_assm_specialized "IH" ["e2"; "env"; "t2"] %> by_solver %> apply_assm "Happ_2"
  |> qed

let canonical_form_thm =
  lambda_thm
  $ unwords
      [ "forall v t :term."
      ; " (Value v) =>"
      ; " (Typing v nil t)  =>"
      ; " (exists a :atom. exists e :term. [v = lam (a.e)] ∧ (Term e))"
      ; " ∧"
      ; " (exists t1 t2 :term. [t =  arrow t1 t2])" ]

let canonical_form =
  proof' canonical_form_thm |> intro %> intro
  |> intros ["Hv"; "Ht"] %> destruct_assm "Ht"
  |> intros' ["contra"; "a"; ""]
     %> ex_falso
     %> apply_thm_specialized empty_contradiction ["a"; "t"]
     %> apply_assm "contra"
  |> intros' ["Hlam"; "a"; "e"; "t1"; "t2"; ""; ""; ""]
  |> destruct_goal
  |> exists "a" %> exists "e" %> by_solver
     %> apply_thm_specialized typing_terms ["e"; "cons a t1 nil"; "t2"]
     %> assumption
  |> exists "t1" %> exists "t2" %> by_solver
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
  |> destruct_assm' "H" [""] |> assumption
  |> apply_thm_specialized canonical_form ["v"; "arrow t1 t2"] %> apply_assm "Hv" %> apply_assm "Ht"
  |> qed

let subst_proper_thm =
  lambda_thm "forall e :term. forall a:atom. forall v e' :term. [a # v] => (Sub e a v e') => (a # e')"

let subst_proper =
  proof' subst_proper_thm
  |> intro %> intro %> intro %> intro %> intro
  |> generalize "e'" |> generalize "e" |> by_induction "e0" "IH" |> intro
  |> intros' ["He"; ""]
  |> intros' ["Ha"; ""]
  |> by_solver
  |> intros' ["Hb"; "b"; ""; ""]
  |> by_solver
  |> intros' ["Hlam"; "b"; "e_b"; "e_b'"; ""; ""; ""; ""]
  |> add_assumption_parse "He_b" "a # e_b'"
  |> by_solver
  |> apply_assm_specialized "IH" ["e_b"; "e_b'"]
  |> by_solver |> apply_assm "Hlam"
  |> intros' ["Happ"; "e1"; "e2"; "e1'"; "e2'"; ""; ""; ""]
  |> add_assumption_parse "H1" "a # e1'" |> add_assumption_parse "H2" "a # e2'" |> by_solver
  |> apply_assm_specialized "IH" ["e2"; "e2'"]
  |> by_solver |> assumption
  |> apply_assm_specialized "IH" ["e1"; "e1'"]
  |> by_solver |> assumption |> qed

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

let subst_proper_thm' =
  lambda_thm "forall e :term. forall a:atom. forall v :term. [a # e] => (Term e) =>\n  (Sub e a v e)"

let subst_proper' =
  proof' subst_proper_thm'
  |> intro %> intro %> intro %> generalize "e" %> by_induction "e0" "IH"
  |> intro %> intros' ["Hterm"; ""] (* case on (Term e) *)
  |> intros' ["Hb"; "b"] %> case "var_diff" %> exists "b" %> repeat by_solver (* e = b *)
  |> intros' ["Hlam"; "b"; "e_b"; ""]
  |> add_assumption_thm "Hfresh" Axiom.exists_fresh
  |> specialize_assm "Hfresh" "Hc" ["v e_b a"]
  |> destruct_assm' "Hc" ["c"] |> case "lam" |> exists "[b c]b" |> exists "[b c]e_b" |> exists "[b c]e_b"
  |> by_solver |> by_solver |> by_solver |> by_solver
  |> apply_assm_specialized "IH" ["[b c]e_b"]
  |> by_solver |> by_solver
  |> apply_thm_specialized swap_lemma ["e_b"; "b"; "c"]
  |> apply_assm "Hlam"
  |> intros' ["Happ"; "e1"; "e2"; ""; ""]
  |> case "app"
  |> exists "e1" %> exists "e2" %> exists "e1" %> exists "e2"
  |> by_solver |> by_solver |> destruct_goal |> apply_assm_specialized "IH" ["e1"] |> by_solver |> by_solver
  |> apply_assm "Happ_1" |> apply_assm_specialized "IH" ["e2"] |> by_solver |> by_solver
  |> apply_assm "Happ_2" |> qed

let subst_exists_thm =
  lambda_thm
  $ unwords
      [ "forall a : atom."
      ; "forall v : term. (Value v) =>"
      ; "forall e : term. (Term e) =>"
      ; "exists e' : term. (Sub e a v e')" ]

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

let progress_thm = lambda_thm "forall e t :term. (Typing e nil t) => (Progressive e)"

let progress =
  proof' progress_thm |> by_induction "e0" "IH" |> intro
  |> intros' ["He"; ""]
  |> intros' ["Ha"; "a"; ""; ""]
     %> intros' ["contra"; ""]
     %> discriminate
     %> intros' ["contra"; "a'"; "t'"; "e'"; ""]
     %> discriminate
  |> intros' ["Hlam"; "a"; "e_a"; "t1"; "t2"; ""; ""; ""]
     %> case "value" %> case "lam"
     %> exists' ["a"; "e_a"]
     %> by_solver
     %> apply_thm_specialized typing_terms ["e_a"; "cons a t1 nil"; "t2"]
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; "t2"; ""; ""]
  |> add_assumption_parse "He1" "Progressive e1"
  |> add_assumption_parse "He2" "Progressive e2"
  |> destruct_assm "He1" %> intros ["Hv1"] %> destruct_assm "He2"
  |> intros ["Hv2"] (* Value e1, Value e2 *)
     %> ( add_assumption_thm_specialized "He1lam" canonical_form' ["e1"; "t2"; "t"]
        %> apply_in_assm "He1lam" "Hv1" %> apply_in_assm "He1lam" "Happ_1"
        %> destruct_assm' "He1lam" ["a"; "e_a"; ""] (* He1lam: [e1 = lam (a.e_a)] ∧ (Term e_a) *) )
     %> ( add_assumption_thm_specialized "He_a" subst_exists ["a"; "e2"; "e_a"]
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
