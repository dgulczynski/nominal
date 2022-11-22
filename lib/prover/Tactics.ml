open Common
open Proof
open Prover
open ProverException
open Printing
open Option

let try_tactic on_fail tactic uproof = try tactic uproof with ProverException e -> on_fail e

let try_tactic' tactic uproof = try_tactic (const uproof) tactic uproof

let try_opt tactic = try_tactic (const none) (some % tactic)

let intros = List.fold_right intro

let try_many on_fail tactics uproof =
  match List.find_map (flip try_opt uproof) tactics with
  | Some success -> success
  | None         -> on_fail ()

let assumption uproof =
  let env, f = goal uproof in
  let exn = Printf.sprintf "No assumption matching goal `%s`" $ string_of_formula f in
  let on_fail _ = raise $ ProverException exn in
  match List.find_opt (equiv f % snd) env with
  | Some (h_name, _) -> apply_assm h_name uproof
  | None             ->
      let tactics = List.map (apply_assm % fst) env in
      try_many on_fail tactics uproof

let contradiction = assumption % ex_falso

let trivial =
  let on_fail _ = raise $ ProverException "This ain't trivial" in
  let tactic = assumption % (try_tactic' $ intro "_") in
  try_tactic on_fail tactic
