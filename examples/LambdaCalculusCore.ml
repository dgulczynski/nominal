open Nominal.Parser
open Nominal.ProverGoal
open Nominal.ProofEnv
open Nominal.Printing

let lambda_symbols = funcs_env ["lam"; "app"; "base"; "arrow"; "nil"; "cons"]

let type_formula =
  unwords
    [ "fix Type(t): * =  "
    ; " base: t = base  "
    ; " ∨   "
    ; " arrow: ( exists t1 t2 :term. [t = arrow t1 t2] ∧ (Type t1) ∧ (Type t2) )" ]

let inenv_formula =
  unwords
    [ "fix InEnv(env): forall a :atom. forall t :term. * = fun a :atom -> fun t :term -> "
    ; " current: ( exists env': term. [env = cons a t env'] ) "
    ; " ∨   "
    ; " next: ( exists b :atom. exists s env': term. [env = cons b s env'] ∧ [a =/= b] ∧ (InEnv env' a {t}))" ]

let typing_formula =
  unwords
    [ "fix Typing(e): forall env t :term. * = fun env :term -> fun t :term -> "
    ; " var: ( exists a :atom.   "
    ; " [e = a] ∧ InEnv {env} a {t} )  "
    ; " ∨   "
    ; " lam: ( exists a :atom. exists e' t1 t2 :term.  "
    ; " [e = lam (a.e')] ∧ [t = arrow t1 t2] ∧ (Type t1) ∧ (Typing {e'} {cons a t1 env} {t2}) )"
    ; " ∨   "
    ; " app: ( exists e1 e2 t2 :term.  "
    ; " [e = app e1 e2] ∧ (Typing {e1} {env} {arrow t2 t}) ∧ (Typing {e2} {env} {t2}) )" ]

let term_formula =
  unwords
    [ "fix Term(e): * = "
    ; " var: ( exists a :atom. [e = a] ) "
    ; " ∨ "
    ; " lam: ( exists a :atom. exists e' :term. [e = lam (a.e')] ∧ (Term e') )"
    ; " ∨ "
    ; " app: ( exists e1 e2 :term. [e = app e1 e2] ∧ (Term e1) ∧ (Term e2) )" ]

let value_formula =
  unwords
    [ "fun e:term -> "
    ; " var: (exists a :atom. [e = a])"
    ; " ∨"
    ; " lam: (exists a :atom. exists e' : term. [e = lam (a.e')] ∧ (Term e'))" ]

let sub_formula =
  unwords
    [ "fix Sub(e): forall a :atom. forall v e':term.* = fun a :atom -> fun v :term -> fun e' :term -> "
    ; " var_same: ([e = a] ∧ [e' = v])"
    ; " ∨"
    ; " var_diff: (exists b :atom. [e = b] ∧ [e' = b] ∧ [a =/= b])"
    ; " ∨"
    ; " lam: (exists b :atom. exists e_b e_b' :term."
    ; " [e = lam (b.e_b)] ∧ [e' = lam (b.e_b')] ∧ [b # v] ∧ [a =/= b] ∧ (Sub e_b a v e_b'))"
    ; " ∨"
    ; " app: (exists e1 e2 e1' e2' :term."
    ; " [e = app e1 e2] ∧ [e' = app e1' e2'] ∧ (Sub e1 a v e1') ∧ (Sub e2 a v e2'))" ]

let step_formula =
  unwords
    [ "fix Steps(e): forall e' :term.* = fun e' :term -> "
    ; " app_l: ( exists e1 e1' e2 :term. "
    ; " [e = app e1 e2] ∧ [e' = app e1' e2] ∧ (Steps e1 e1')) "
    ; " ∨ "
    ; " app_r: ( exists v e2 e2' :term. "
    ; " [e = app v e2] ∧ [e' = app v e2'] ∧ (Value v) ∧ (Steps e2 e2'))"
    ; " ∨ "
    ; " app: ( exists a :atom. exists e_a v :term. "
    ; " [e = app (lam (a.e_a)) v] ∧ (Value v) ∧ (Sub e_a a v e'))" ]

let progressive_formula =
  unwords
    [ "fun e:term ->                        "
    ; "  value: (Value e)                   "
    ; "  ∨                                  "
    ; "  steps: (exists e':term. Steps e e')" ]

let env_inclusion_formula =
  unwords
    [ "fun env1 : term -> fun env2 : term ->"
    ; "  forall a : atom. forall t : term."
    ; "  (InEnv env1 a t) => (InEnv env2 a t)" ]

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

let lambda_thm thm : goal = (lambda_env, parse_formula lambda_env thm)
