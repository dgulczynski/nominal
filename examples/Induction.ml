open Nominal.Prelude
open Nominal.Prover
open Nominal.Tactics

let ind_weak_thm =
  theorem
  $ unwords
      [ "forall P : (forall t :term. prop).    "
      ; "forall t : term.                      "
      ; "  (forall a :atom.                    "
      ; "     P {a}) =>                        "
      ; "  (forall t1 t2 :term.                "
      ; "     (P t1) => (P t2) => P {t1 t2}) =>"
      ; "  (forall a :atom. forall e :term.    "
      ; "     (P e) => P {a.e}) =>             "
      ; "  (forall s :term.                    "
      ; "     [symbol s] => P s) =>            "
      ; "   P t" ]

let ind_strong'_thm =
  theorem
  $ unwords
      [ "forall P : (forall t :term. prop).                "
      ; "forall t : term.                                  "
      ; "  (forall a :atom.                                "
      ; "     P {a}) =>                                    "
      ; "  (forall t1 t2 :term.                            "
      ; "     (P t1) => (P t2) => P {t1 t2}) =>            "
      ; "  (forall c :term. forall a :atom. forall e :term."
      ; "     [a # c] => (P e) => P {a.e}) =>              "
      ; "  (forall s :term.                                "
      ; "     [symbol s] => P s) =>                        "
      ; "   P t" ]

let ind_strong_thm =
  theorem
  $ unwords
      [ "forall P : (forall c t :term. prop).                                            "
      ; "forall context t : term.                                                        "
      ; "  (forall c :term. forall a :atom.                                              "
      ; "     P c {a}) =>                                                                "
      ; "  (forall c :term. forall t1 t2 :term.                                          "
      ; "     (forall c' :term. P c' t1) => (forall c' :term. P c' t2) => P c {t1 t2}) =>"
      ; "  (forall c :term. forall a :atom. forall e :term.                              "
      ; "     [a # c] => (forall c' :term. P c' e) => P c {a.e}) =>                      "
      ; "  (forall c :term. forall s :term.                                              "
      ; "     [symbol s] => P c s) =>                                                    "
      ; "   P context t" ]

let ind_strong =
  proof' ind_strong_thm
  |> repeat intro %> intros ["Hatom"; "Happ"; "Hlam"; "Hsym"]
  |> generalize "context" %> generalize "t" %> by_induction "t'" "IH" %> intro %> inverse_term "t"
  |> intros' ["H"; "a"] %> apply_assm_spec "Hatom" ["context"; "a"]
  |> intros' ["H"; "a"; "e"]
     %> get_fresh_atom "b" "context e"
     %> apply_assm_spec "Hlam" ["context"; "b"; "[a b]e"]
     %> solve
     %> apply_assm_spec "IH" ["[a b]e"]
     %> solve
  |> intros' ["H"; "e1"; "e2"]
     %> apply_assm_spec "Happ" ["context"; "e1"; "e2"]
     %> apply_assm_spec "IH" ["e1"]
     %> solve
     %> apply_assm_spec "IH" ["e2"]
     %> solve
  |> intros' ["H"] %> apply_assm_spec "Hsym" ["context"; "t"] %> solve
  |> qed

let ind_strong' =
  proof' ind_strong'_thm
  |> repeat intro %> intros ["Hatom"; "Happ"; "Hlam"; "Hsym"]
  |> get_fresh_atom "context" "t" (* generate fresh atom as an artificial context to use with strong induction *)
  |> apply_thm_spec ind_strong ["fun _ e :term -> P e"; "context"; "t"]
  |> intros ["c"] %> assumption
  |> intros ["c"; "t1"; "t2"; "Ht1"; "Ht2"]
     %> apply_assm_spec "Happ" ["t1"; "t2"]
     %> apply_assm_spec "Ht1" ["context"]
     %> apply_assm_spec "Ht2" ["context"]
  |> intros ["c"; "a"; "e"]
     %> intro
     %> intros ["He"]
     %> apply_assm_spec "Hlam" ["c"; "a"; "e"]
     %> solve
     %> apply_assm_spec "He" ["c"]
  |> intros ["c"; "s"] %> intro %> apply_assm_spec "Hsym" ["s"] %> solve
  |> qed

let ind_weak =
  proof' ind_weak_thm
  |> repeat intro %> intros ["Hatom"; "Happ"; "Hlam"; "Hsym"]
  |> apply_thm_spec ind_strong' ["P"; "t"]
  |> apply_assm "Hatom"
  |> apply_assm "Happ"
  |> intros ["c"; "a"; "e"] %> intro %> apply_assm_spec "Hlam" ["a"; "e"]
  |> apply_assm "Hsym"
  |> qed
