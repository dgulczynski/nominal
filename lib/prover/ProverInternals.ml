open Types
open Common
open Proof
open IncProof
open ProofContext
open ProofPrinting
open ProofException

(** Type of in-progress proof of [Prover] *)
type prover_state = U_Unfinished of {goal: goal; context: proof_context} | U_Finished of incproof

type tactic = prover_state -> prover_state

let unproven goal =
  let exn = Printf.sprintf "You haven't proven `%s` yet!" $ string_of_goal goal in
  ProofException exn

(** Helper function that traverses [iproof] and returns [U_Unfinished {goal; context}] of a first found [PI_Hole goal] 
    (where [context] is its context in [iproof]) or [U_Finished iproof] if [iproof] has no holes *)
let rec find_goal_in_proof context = function
  | PI_Axiom _ as iproof -> find_goal_in_ctx iproof context
  | PI_Hole goal -> U_Unfinished {goal; context}
  | PI_Intro (jgmt, iproof) -> find_goal_in_proof (PC_Intro (jgmt, context)) iproof
  | PI_ExFalso (jgmt, ipp) -> find_goal_in_proof (PC_ExFalso (jgmt, context)) ipp
  | PI_Apply (jgmt, lproof, rproof) when hasHoles lproof ->
      find_goal_in_proof (PC_ApplyLeft (jgmt, context, rproof)) lproof
  | PI_Apply (jgmt, lproof, rproof) when hasHoles rproof ->
      find_goal_in_proof (PC_ApplyRight (jgmt, lproof, context)) rproof
  | PI_Apply _ as iproof -> find_goal_in_ctx iproof context

(** Helper functions that given [iproof] and its [contex] builds appropriate [state] *)
and find_goal_in_ctx iproof = function
  | PC_Root when hasHoles iproof -> find_goal_in_proof PC_Root iproof
  | PC_Root -> U_Finished iproof
  | PC_Intro (jgmt, ctx) -> find_goal_in_ctx $ PI_Intro (jgmt, iproof) $ ctx
  | PC_ApplyRight (jgmt, lproof, rctx) -> find_goal_in_ctx $ PI_Apply (jgmt, lproof, iproof) $ rctx
  | PC_ApplyLeft (jgmt, lctx, rproof) -> find_goal_in_ctx $ PI_Apply (jgmt, iproof, rproof) $ lctx
  | PC_ExFalso (jgmt, ctx) -> find_goal_in_ctx $ PI_ExFalso (jgmt, iproof) $ ctx

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
  | U_Finished _           -> raise finished
  | U_Unfinished {goal; _} -> goal

let context = function
  | U_Finished _              -> raise finished
  | U_Unfinished {context; _} -> context

let env_of = fst

let formula_of = snd

let goal_env = env_of % goal

let goal_formula = formula_of % goal

let lookup env h_name =
  match List.assoc_opt h_name env with
  | None   -> raise $ unknown_hypothesis h_name
  | Some h -> h

let premise = function
  | F_Impl (p, _) -> p
  | f             -> raise $ not_an_implication f

let conclusion = function
  | F_Impl (_, c) -> c
  | f             -> raise $ not_an_implication f

let apply_internal h_proof h_name =
  let apply_impl_list env =
    List.fold_left (fun iproof f ->
        PI_Apply (to_judgement (env, conclusion f), hole env (premise f), iproof) )
  in
  let h = label' h_proof in
  function
  | U_Finished _ -> raise finished
  | U_Unfinished {goal= _, f; context} when f === h -> find_goal_in_ctx h_proof context
  | U_Unfinished {goal= env, f; context} -> (
    match destruct_impl f h with
    | []    -> raise $ hypothesis_goal_mismatch h_name h f
    | assms -> find_goal_in_proof context $ apply_impl_list env h_proof assms )

(** "Smart" constructor for proof state. Notice that there is no constructor of [U_Finished] state available for the user, as only the [ProverInternals] can finish a proof. *)
let unfinished goal context = U_Unfinished {goal; context}

let finish = function
  | U_Unfinished {goal; _} -> raise $ unproven goal
  | U_Finished iproof      -> iproof