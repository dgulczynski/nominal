open Types
open Common
open Printing
open Proof
open IncProof
open ProofContext

(** Type of in-progress proof of [Prover] *)
type uproof = U_Unfinished of goal * proof_context | U_Finished of incproof

let raise_unproven f = failwith $ Printf.sprintf "You haven't proven %s yet!" (string_of_formula f)

let raise_unknown_hypothesis h = failwith $ Printf.sprintf "Hypothesis %s\n not in environment" h

let raise_finished () = failwith "Proof finished"

let raise_hypothesis_doesnt_match_goal h_name h_formula goal =
  failwith
  $ Printf.sprintf "Hypothesis of %s is %s, but goal is %s" h_name (string_of_formula h_formula)
      (string_of_formula goal)

(** Helper function that traverses [iproof] and returns [U_Unfinished (goal, ctx)] of a first found [PI_Hole goal] 
    (where [ctx] is its context in [iproof]) or [U_Finished iproof] if [iproof] has no holes*)
let rec find_goal ctx = function
  | PI_Axiom _ as iproof -> destack iproof ctx
  | PI_Hole goal -> U_Unfinished (goal, ctx)
  | PI_Intro (jgmt, iproof) -> find_goal (PC_Intro (jgmt, ctx)) iproof
  | PI_ExFalso (jgmt, ipp) -> find_goal (PC_ExFalso (jgmt, ctx)) ipp
  | PI_Apply (jgmt, lproof, rproof) when hasHoles lproof ->
      find_goal (PC_ApplyLeft (jgmt, ctx, rproof)) lproof
  | PI_Apply (jgmt, lproof, rproof) when hasHoles rproof ->
      find_goal (PC_ApplyRight (jgmt, lproof, ctx)) rproof
  | PI_Apply _ as iproof -> destack iproof ctx

(** Helper functions that given [iproof] and its [contex] builds appropriate [uproof]*)
and destack iproof = function
  | PC_Root when hasHoles iproof -> find_goal PC_Root iproof
  | PC_Root -> U_Finished iproof
  | PC_Intro (jgmt, ctx) -> destack $ PI_Intro (jgmt, iproof) $ ctx
  | PC_ApplyRight (jgmt, lproof, rctx) -> destack $ PI_Apply (jgmt, lproof, iproof) $ rctx
  | PC_ApplyLeft (jgmt, lctx, rproof) -> destack $ PI_Apply (jgmt, iproof, rproof) $ lctx
  | PC_ExFalso (jgmt, ctx) -> destack $ PI_ExFalso (jgmt, iproof) $ ctx

(** [destruct_impl c f] is
    [Some [f1 => f2 => ... fn => c; f2 => ... fn => c; ...; fn => c]] if [f = f1 => f2 => ... => fn => c]
    and [[]]] otherwise *)
let destruct_impl conclusion f =
  let rec aux = function
    | F_Impl (_, F_Bot) as f -> Some [f]
    | F_Impl (_, f2) as f when f2 === conclusion -> Some [f]
    | F_Impl (_, f2) as f -> List.cons f <$> aux f2
    | _ -> None
  in
  match aux f with
  | None    -> []
  | Some fs -> fs

let proof env f =
  let goal = (env_to_goal_env env, f) in
  U_Unfinished (goal, PC_Root)

let proof' = uncurry proof

let intro h = function
  | U_Unfinished (((env, f) as goal), ctx) -> (
    match f with
    | F_Impl (f1, f2) ->
        let goal' = (env_add h f1 env, f2) in
        U_Unfinished (goal', PC_Intro (goal_to_judgement goal, ctx))
    | _               -> failwith $ Printf.sprintf "%s is not an implication" (string_of_formula f)
    )
  | U_Finished _ -> raise_finished ()

let apply_assm h =
  let rec apply_assm_list env iproof = function
    | []                    -> iproof
    | F_Impl (h, g) :: rest ->
        apply_assm_list env (PI_Apply (goal_to_judgement (env, g), PI_Hole (env, h), iproof)) rest
    | _                     -> assert false
  in
  function
  | U_Finished _                 -> raise_finished ()
  | U_Unfinished ((env, f), ctx) -> (
    match List.assoc_opt h env with
    | None -> raise_unknown_hypothesis h
    | Some g when f === g -> destack (PI_Axiom (goal_to_judgement (env, f))) ctx
    | Some g -> (
      match destruct_impl f g with
      | []              -> raise_hypothesis_doesnt_match_goal h g f
      | h :: _ as assms ->
          find_goal ctx (apply_assm_list env (PI_Axiom (goal_to_judgement (env, h))) assms) ) )

let qed = function
  | U_Unfinished ((env, F_Top), _) -> PI_Axiom (goal_env_to_env env, F_Top)
  | U_Unfinished ((_, f), _)       -> raise_unproven f
  | U_Finished iproof              -> (
    match find_goal PC_Root iproof with
    | U_Finished _             -> iproof
    | U_Unfinished ((_, f), _) -> raise_unproven f )
