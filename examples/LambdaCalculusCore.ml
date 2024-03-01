open Nominal.Prelude
open Nominal.Parser
open Nominal.Prover
open Nominal.ProofEnv
open Nominal.Tactics

let lambda_symbols = symbols ["lam"; "app"; "base"; "arrow"; "nil"; "cons"]

let type_formula =
  {|
    fix Type(t): * =
      base: t = base
      ∨
      arrow: ( exists t1 t2 :term. [t = arrow t1 t2] ∧ (Type t1) ∧ (Type t2) )
  |}

let inenv_formula =
  {|
    fix InEnv(env): forall a :atom. forall t :term. * = fun (a :atom) (t :term) ->
      current: ( exists env': term. [env = cons a t env'] )
      ∨
      next: ( exists b :atom. exists s env': term.
                [env = cons b s env'] ∧ [a =/= b] ∧ (InEnv env' a {t}) )
  |}

let typing_formula =
  {|
    fix Typing(e): forall env t :term. * = fun env t :term ->
     var: ( exists a :atom.
              [e = a] ∧ InEnv {env} a {t} )
     ∨
     lam: ( exists a :atom. exists e' t1 t2 :term.
              [e = lam (a.e')] ∧ [t = arrow t1 t2]
                   ∧ (Type t1) ∧ (Typing {e'} {cons a t1 env} {t2}) )
     ∨
     app: ( exists e1 e2 t2 :term.
              [e = app e1 e2] ∧ (Typing {e1} {env} {arrow t2 t})
                              ∧ (Typing {e2} {env} {t2}) )
  |}

let term_formula =
  {|
    fix Term(e): * =
     var: ( exists a :atom. [e = a] )
     ∨
     lam: ( exists a :atom. exists e' :term. [e = lam (a.e')] ∧ (Term e') )
     ∨
     app: ( exists e1 e2 :term. [e = app e1 e2] ∧ (Term e1) ∧ (Term e2) )
  |}

let value_formula =
  {|
    fun e:term ->
      var: (exists a :atom. [e = a])
      ∨
      lam: (exists a :atom. exists e' : term. [e = lam (a.e')])
  |}

let sub_formula =
  {|
    fix Sub(e): forall a :atom. forall v e' :term.* = fun (a :atom) (v e' :term) ->
      var_same: ([e = a] ∧ [e' = v])
      ∨
      var_diff: (exists b :atom. [e = b] ∧ [e' = b] ∧ [a =/= b])
      ∨
      lam: (exists b :atom. exists e_b e_b' :term.
             [e = lam (b.e_b)] ∧ [e' = lam (b.e_b')]
                ∧ [b # v] ∧ [a =/= b] ∧ (Sub e_b a v e_b'))
      ∨
      app: (exists e1 e2 e1' e2' :term.
             [e = app e1 e2] ∧ [e' = app e1' e2'] ∧ (Sub e1 a v e1') ∧ (Sub e2 a v e2'))
  |}

let step_formula =
  {|
    fix Steps(e): forall e' :term.* = fun e' :term ->
      app_l: ( exists e1 e1' e2 :term.
          [e = app e1 e2] ∧ [e' = app e1' e2] ∧ (Steps e1 e1'))
      ∨
      app_r: ( exists v e2 e2' :term.
          [e = app v e2] ∧ [e' = app v e2'] ∧ (Value v) ∧ (Steps e2 e2'))
      ∨
      app: ( exists a :atom. exists e_a v :term.
          [e = app (lam (a.e_a)) v] ∧ (Value v) ∧ (Sub e_a a v e'))
  |}

let progressive_formula =
  {|
    fun e:term ->
      value: (Value e)
      ∨
      steps: (exists e':term. Steps e e')
  |}

let env_inclusion_formula =
  {|
    fun env1 env2 : term ->
      forall a : atom. forall t : term.
        (InEnv env1 a t) => (InEnv env2 a t)
  |}

let lambda_env =
  parse_mapping lambda_symbols [] [] snd
    [ ("Type", type_formula)
    ; ("InEnv", inenv_formula)
    ; ("EnvInclusion", env_inclusion_formula)
    ; ("Typing", typing_formula)
    ; ("Term", term_formula)
    ; ("Value", value_formula)
    ; ("Sub", sub_formula)
    ; ("Steps", step_formula)
    ; ("Progressive", progressive_formula) ]

let lambda_identifiers = all_identifiers lambda_env

let lambda_thm = theorem' lambda_env % String.trim

let term_involutive_thm = lambda_thm {|
  forall t :term. forall a a' :atom.
     (Term t) => (Term {[a a']t})
  |}

let term_involutive =
  proof' term_involutive_thm
  |> by_induction "t'" "IH" %> repeat intro %> intro'
  |> intros' ["H"; "b"] %> (case "var" %> exists "[a a']b" %> solve)
  |> intros' ["H"; "b"; "e"; ""]
     %> (case "lam" %> exists' ["[a a']b"; "[a a']e"] %> solve)
     %> (apply_assm_spec "IH" ["e"; "a"; "a'"] %> solve %> apply_assm "H")
  |> intros' ["H"; "e1"; "e2"; ""; ""]
     %> (case "app" %> exists' ["[a a']e1"; "[a a']e2"] %> solve %> destruct_goal)
     %> (apply_assm_spec "IH" ["e1"; "a"; "a'"] %> solve %> apply_assm "H_1")
     %> (apply_assm_spec "IH" ["e2"; "a"; "a'"] %> solve %> apply_assm "H_2")
  |> qed

let lambda_ind_thm =
  lambda_thm
    {|
    forall P : (forall t :term. prop).
    forall ctx e : term.
      (forall a :atom.
         P {a}) =>
      (forall t1 t2 :term.
         (Term t1) => (P t1) => (Term t2) => (P t2) => P {app t1 t2}) =>
      (forall a :atom. forall e :term.
         [a # ctx] => (Term e) => (P e) => P {lam (a.e)}) =>
      (Term e) =>
       P e
  |}

let swap_term_lemma_thm = lambda_thm "forall e : term. forall a b : atom. (Term e) => (Term {[a b]e})"

let swap_term_lemma =
  proof' swap_term_lemma_thm
  |> by_induction "e0" "IH" %> repeat intro %> intro'
  |> intros' ["Hc"; "c"] %> case "var" %> exists "[a b]c" %> solve
  |> intros' ["Hlam"; "c"; "e_c"; ""]
     %> case "lam"
     %> exists' ["[a b]c"; "[a b]e_c"]
     %> solve
     %> apply_assm_spec "IH" ["e_c"; "a"; "b"]
     %> solve
     %> assumption
  |> intros' ["Happ"; "e1"; "e2"; ""; ""]
     %> case "app"
     %> exists' ["[a b]e1"; "[a b]e2"]
     %> solve
     %> destruct_goal
     %> apply_assm_spec "IH" ["e1"; "a"; "b"]
     %> solve
     %> assumption
     %> apply_assm_spec "IH" ["e2"; "a"; "b"]
     %> solve
     %> assumption
  |> qed

let lambda_ind =
  proof' lambda_ind_thm
  |> repeat intro %> intros ["Hvar"; "Happ"; "Hlam"]
  |> generalize "e" %> by_induction "e'" "IH" %> intro'
  |> intros' ["Ha"; "a"] %> apply_assm_spec "Hvar" ["a"]
  |> intros' ["Hae"; "a"; "e_a"; ""]
  |> get_fresh_atom "b" "ctx e_a"
     %> apply_assm_spec "Hlam" ["b"; "[a b]e_a"]
     %> solve
     %> (apply_thm_spec swap_term_lemma ["e_a"; "a"; "b"] %> apply_assm "Hae")
     %> apply_assm_spec "IH" ["[a b]e_a"]
     %> solve
     %> (apply_thm_spec swap_term_lemma ["e_a"; "a"; "b"] %> apply_assm "Hae")
  |> intros' ["He"; "e1"; "e2"; ""; ""]
     %> apply_assm_spec "Happ" ["e1"; "e2"]
     %> (apply_assm "He_1" %> apply_assm_spec "IH" ["e1"] %> solve %> apply_assm "He_1")
     %> (apply_assm "He_2" %> apply_assm_spec "IH" ["e2"] %> solve %> apply_assm "He_2")
  |> qed

let lambda_ind'_thm =
  lambda_thm
    {|
      ∀ P :(∀ _ :term. *).
           (∀ a :atom. P {a})
        => (∀ t1 t2 :term.
                (Term t1) => (Term t2)
             => (P t1) => (P t2)
             => P {app t1 t2})
       => (∀ a :atom. ∀ t :term.
                (Term t)
             => (∀ c :term. ∃ a' :atom. ∃ t' :term. (Term t') ∧
                  ([a' # c] ∧ [a.t = a'.t'] ∧ P t'))
             => P {lam (a.t)})
        => (∀ t :term. (Term t) => P t)
    |}

let lambda_ind' =
  proof' lambda_ind'_thm
  |> repeat intro %> intros ["Hvar"; "Happ"; "Hlam"; "e"] %> generalize "e" %> by_induction "e'" "IH" %> intro'
  |> intros' ["H"; "a"] %> apply_assm_spec "Hvar" ["a"]
  |> intros' ["H"; "a"; "e'"; ""]
     %> apply_assm_spec "Hlam" ["a"; "e'"]
     %> apply_assm "H"
     %> (intros ["ctx"] %> get_fresh_atom "a'" "ctx e'" %> exists' ["a'"] %> exists "[a a']e'")
     %> destruct_goal
     %> (apply_thm_spec term_involutive ["e'"; "a'"; "a"] %> apply_assm "H")
     %> repeat solve
     %> (apply_assm_spec "IH" ["[a a']e'"] %> solve)
     %> (apply_thm_spec term_involutive ["e'"; "a'"; "a"] %> apply_assm "H")
  |> intros' ["H"; "e1"; "e2"; ""; ""]
     %> apply_assm_spec "Happ" ["e1"; "e2"]
     %> apply_assm "H_1"
     %> apply_assm "H_2"
     %> (apply_assm_spec "IH" ["e1"] %> solve %> apply_assm "H_1")
     %> (apply_assm_spec "IH" ["e2"] %> solve %> apply_assm "H_2")
  |> qed

let lambda_ind''_thm =
  lambda_thm
    {|
      ∀ P :(∀ _ :term. *).
           (∀ a :atom. P {a})
        => (∀ t1 t2 :term.
                (Term t1) => (Term t2)
             => (P t1) => (P t2)
             => P {app t1 t2})
        => (∀ a :atom. ∀ e :term.
                (Term e)
             => (∀ c :term. ∀ a' :atom. ∀ e' :term.
                     [a' # c] => [a.e = a'.e'] => P e')
             => P {lam (a.e)})
        => (∀ t :term. (Term t) => P t)
    |}

let lambda_ind'' =
  proof' lambda_ind''_thm
  |> repeat intro %> intros ["Hvar"; "Happ"; "Hlam"; "e"] %> generalize "e" %> by_induction "e'" "IH" %> intro'
  |> intros' ["H"; "a"] %> apply_assm_spec "Hvar" ["a"]
  |> intros' ["H"; "a"; "t"; ""]
     %> apply_assm_spec "Hlam" ["a"; "t"]
     %> apply_assm "H"
     %> repeat intro
     %> apply_assm_spec "IH" ["e'"]
     %> solve
     %> apply_thm_spec term_involutive ["t"; "a"; "a'"]
     %> apply_assm "H"
  |> intros' ["H"; "e1"; "e2"; ""; ""]
     %> apply_assm_spec "Happ" ["e1"; "e2"]
     %> apply_assm "H_1"
     %> apply_assm "H_2"
     %> (apply_assm_spec "IH" ["e1"] %> solve %> apply_assm "H_1")
     %> (apply_assm_spec "IH" ["e2"] %> solve %> apply_assm "H_2")
  |> qed
