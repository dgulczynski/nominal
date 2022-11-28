open Common
open ProofException
open Prover
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
  match ProofEnv.lookup env (equiv f % snd) with
  | Some (h_name, _) -> apply_assm h_name state
  | None             ->
      let to_tactic = apply_assm % fst in
      let tactics = List.map to_tactic $ ProofEnv.to_list env in
      try_many on_fail tactics state

let contradiction = assumption % ex_falso

let trivial =
  let on_fail _ = raise $ ProofException "This ain't trivial" in
  try_many on_fail [assumption % intro "_"; assumption]
