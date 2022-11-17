open Types
open Common
open Proof
open IncProof
open ProofContext
open ProofPrinting
open ProverException

let unproven goal =
  let exn = Printf.sprintf "You haven't proven `%s` yet!" $ string_of_goal goal in
  ProverException exn

(** Type of in-progress proof of [Prover] *)
type uproof = U_Unfinished of goal * proof_context | U_Finished of incproof

(** Helper function that traverses [iproof] and returns [U_Unfinished (goal, ctx)] of a first found [PI_Hole goal] 
    (where [ctx] is its context in [iproof]) or [U_Finished iproof] if [iproof] has no holes*)
let rec find_goal_in_proof ctx = function
  | PI_Axiom _ as iproof -> find_goal_in_ctx iproof ctx
  | PI_Hole goal -> U_Unfinished (goal, ctx)
  | PI_Intro (jgmt, iproof) -> find_goal_in_proof (PC_Intro (jgmt, ctx)) iproof
  | PI_ExFalso (jgmt, ipp) -> find_goal_in_proof (PC_ExFalso (jgmt, ctx)) ipp
  | PI_Apply (jgmt, lproof, rproof) when hasHoles lproof ->
      find_goal_in_proof (PC_ApplyLeft (jgmt, ctx, rproof)) lproof
  | PI_Apply (jgmt, lproof, rproof) when hasHoles rproof ->
      find_goal_in_proof (PC_ApplyRight (jgmt, lproof, ctx)) rproof
  | PI_Apply _ as iproof -> find_goal_in_ctx iproof ctx

(** Helper functions that given [iproof] and its [contex] builds appropriate [uproof]*)
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

let proof env f =
  let goal = (to_goal_env env, f) in
  U_Unfinished (goal, PC_Root)

let proof' = uncurry proof

let goal = function
  | U_Finished _           -> raise finished
  | U_Unfinished (goal, _) -> goal

let goal_env = fst % goal

let lookup env h_name =
  match List.assoc_opt h_name env with
  | None   -> raise $ unknown_hypothesis h_name
  | Some h -> h

let hole env f = PI_Hole (env, f)

let axiom env f = PI_Axiom (to_env env, f)

let premise = function
  | F_Impl (p, _) -> p
  | f             -> raise $ not_an_implication f

let conclusion = function
  | F_Impl (_, c) -> c
  | f             -> raise $ not_an_implication f

let apply' h_proof h_name =
  let apply_impl_list env =
    List.fold_left (fun iproof f ->
        PI_Apply (to_judgement (env, conclusion f), hole env (premise f), iproof) )
  in
  let h = label' h_proof in
  function
  | U_Finished _ -> raise finished
  | U_Unfinished ((_, f), ctx) when f === h -> find_goal_in_ctx h_proof ctx
  | U_Unfinished ((env, f), ctx) -> (
    match destruct_impl f h with
    | []    -> raise $ hypothesis_goal_mismatch h_name h f
    | assms -> find_goal_in_proof ctx $ apply_impl_list env h_proof assms )

let intro h = function
  | U_Unfinished (((env, f) as goal), ctx) -> (
    match f with
    | F_Impl (f1, f2) ->
        let goal' = (env_add h f1 env, f2) in
        U_Unfinished (goal', PC_Intro (to_judgement goal, ctx))
    | _               -> raise $ not_an_implication f )
  | U_Finished _ -> raise finished

let intros = List.fold_right intro

let apply h uproof =
  let env = goal_env uproof in
  apply' (hole env h) None uproof

let apply_thm iproof uproof = apply' iproof None uproof

let apply_assm h_name uproof =
  let env = goal_env uproof in
  let h = lookup env h_name in
  apply' (axiom env h) (Some h_name) uproof

let ex_falso = function
  | U_Finished _                 -> raise finished
  | U_Unfinished ((env, f), ctx) -> U_Unfinished ((env, F_Bot), PC_ExFalso ((to_env env, f), ctx))

let qed = function
  | U_Unfinished ((env, F_Top), _) -> axiom env F_Top
  | U_Unfinished (goal, _)         -> raise $ unproven goal
  | U_Finished iproof              -> (
    match find_goal_in_proof PC_Root iproof with
    | U_Finished _           -> iproof
    | U_Unfinished (goal, _) -> raise $ unproven goal )
