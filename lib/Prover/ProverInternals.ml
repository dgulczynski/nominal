open Types
open Common
open IncProof
open Proof
open ProofEnv
open ProofCommon
open ProofException
open ProverGoal

(** Type of in-progress proof of [Prover] *)
type prover_state = S_Unfinished of {goal: goal; context: proof_context} | S_Finished of proof

(** "Smart" constructor for proof state.
    Notice that there is no constructor of [S_Finished] state available for the user, as only the [ProverInternals] can finish a proof. *)
let unfinished goal context = S_Unfinished {goal; context}

let finished proof = S_Finished proof

type tactic = prover_state -> prover_state

let unproven goal =
  let exn = Printf.sprintf "You haven't proven `%s` yet!" $ string_of_goal goal in
  ProofException exn

(** Helper function that traverses [incproof] and returns [S_Unfinished {goal; context}] of a first found hole 
    (where [context] is its context in [incproof]) or [S_Finished incproof] if [incproof] has no holes *)
let rec find_goal_in_proof context incproof =
  match find_hole_in_proof context incproof with
  | Either.Left (proof, context) -> find_goal_in_ctx (proven proof) context
  | Either.Right (goal, context) -> unfinished goal context

(** Helper functions that given [incproof] and its [contex] builds appropriate [state] *)
and find_goal_in_ctx incproof = function
  | PC_Root -> proof_case finished (find_goal_in_proof PC_Root) incproof
  | PC_Intro (jgmt, ctx) -> find_goal_in_ctx (proof_intro jgmt incproof) ctx
  | PC_ApplyRight (jgmt, lproof, rctx) -> find_goal_in_ctx (proof_apply jgmt lproof incproof) rctx
  | PC_ApplyLeft (jgmt, lctx, rproof) -> find_goal_in_ctx (proof_apply jgmt incproof rproof) lctx
  | PC_ExFalso (jgmt, ctx) -> find_goal_in_ctx (proof_ex_falso jgmt incproof) ctx

(** [destruct_impl c f] is
    [Some [f1 => f2 => ... fn => c; f2 => ... fn => c; ...; fn => c]] if [f = f1 => f2 => ... => fn => c]
    and [[]] otherwise *)
let destruct_impl conclusion f =
  let rec aux = function
    | F_Impl (_, f2) as f when f2 === conclusion -> Some [f]
    | F_Impl (_, f2) as f -> List.cons f <$> aux f2
    | _ -> None
  in
  match aux f with
  | None    -> []
  | Some fs -> fs

let goal = function
  | S_Finished _           -> raise proof_finished
  | S_Unfinished {goal; _} -> goal

let context = function
  | S_Finished _              -> raise proof_finished
  | S_Unfinished {context; _} -> context

let env_of = fst

let formula_of = snd

let goal_env = env_of % goal

let goal_formula = formula_of % goal

let lookup env h_name =
  let test (name, _) = h_name = name in
  match lookup_assumption test env with
  | None        -> raise $ unknown_hypothesis h_name
  | Some (_, h) -> h

let apply_internal ?(h_name = "") h_proof =
  let apply_impl_list env =
    let apply_next imp_proof f =
      let premise_proof = proof_hole env (premise f) in
      let judgement = to_judgement (env, conclusion f) in
      proof_apply judgement imp_proof premise_proof
    in
    List.fold_left apply_next
  in
  let h = label' h_proof in
  function
  | S_Finished _ -> raise proof_finished
  | S_Unfinished {goal= _, f; context} when f === h -> find_goal_in_ctx h_proof context
  | S_Unfinished {goal= env, f; context} -> (
    match destruct_impl f h with
    | []    -> raise $ hypothesis_goal_mismatch h_name h f
    | assms -> find_goal_in_proof context $ apply_impl_list env h_proof assms )

let finish = function
  | S_Unfinished {goal; _} -> raise $ unproven goal
  | S_Finished proof       -> proof
