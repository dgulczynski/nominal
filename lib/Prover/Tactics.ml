open Common
open Proof
open Prover
open ProofException
open ProverInternals
open Printing
open Option

let proof' = uncurry proof

let try_tactic' on_fail tactic state = try tactic state with ProofException e -> on_fail e

let try_tactic tactic state = try_tactic' (const state) tactic state

let try_opt tactic = try_tactic' (const none) (some % tactic)

let intros = List.fold_right intro

let try_many on_fail tactics state =
  match List.find_map (flip try_opt state) tactics with
  | Some success -> success
  | None         -> on_fail ()

let assumption state =
  let env, f = goal state in
  let exn = Printf.sprintf "No assumption matching goal `%s`" $ string_of_formula f in
  let on_fail _ = raise $ ProofException exn in
  match List.find_opt (equiv f % snd) env with
  | Some (h_name, _) -> apply_assm h_name state
  | None             ->
      let tactics = List.map (apply_assm % fst) env in
      try_many on_fail tactics state

let contradiction = assumption % ex_falso

let trivial =
  let on_fail _ = raise $ ProofException "This ain't trivial" in
  let tactic = assumption % (try_tactic $ intro "_") in
  try_tactic on_fail tactic
