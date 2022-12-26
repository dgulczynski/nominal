open Common
open Parser
open ProofCommon
open ProofException
open Prover
open ProverInternals
open Printing
open Option

let proof' = uncurry proof

let try_tactic' on_fail tactic state = try tactic state with ProofException e -> on_fail e

let try_tactic tactic state = state |> try_tactic' (const state) tactic

let try_opt tactic = try_tactic' (const none) (some % tactic)

let intros = flip (List.fold_left (flip intro))

let try_many on_fail tactics state =
  match List.find_map (flip try_opt state) tactics with
  | Some success -> success
  | None         -> on_fail ()

let add_assumption h_name h state =
  let _, f = goal state in
  state |> apply (F_Impl (h, f)) |> intro h_name

let add_assumption_parse h_name h_string state =
  let env, _ = goal state in
  let h = parse_formula_in_env (ProofEnv.identifiers env) h_string in
  state |> add_assumption h_name h

let add_constr c state =
  let _, f = goal state in
  state |> apply (F_ConstrImpl (c, f)) |> intro_constr

let add_constr_parse c_string state =
  let env, _ = goal state in
  let c = parse_constr_in_env (ProofEnv.identifiers env) c_string in
  state |> add_constr c

let assumption state =
  let env, f = goal state in
  let f' = string_of_formula_in_env (ProofEnv.identifiers env) f in
  let exn = Printf.sprintf "No assumption matching goal `%s`" f' in
  let on_fail _ = raise $ ProofException exn in
  match ProofEnv.lookup_assumption (equiv f % snd) env with
  | Some (h_name, _) -> apply_assm h_name state
  | None             ->
      let to_tactic = apply_assm % fst in
      let assumptions = ProofEnv.assumptions env in
      let tactics = List.map to_tactic assumptions in
      state |> try_many on_fail tactics

let contradiction = assumption % ex_falso

let rec repeat tactic state =
  match state |> try_opt tactic with
  | Some state -> repeat tactic state
  | None       -> state

let trivial =
  let on_fail _ = raise $ ProofException "This ain't trivial" in
  try_many on_fail [intro "_" %> assumption; assumption; truth; intro_constr]

let apply_parse f_string state =
  let env, _ = goal state in
  let f = parse_formula_in_env (ProofEnv.identifiers env) f_string in
  state |> apply f
