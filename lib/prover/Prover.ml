open Types
open Common
open Printing
open Proof
open IncProof
open ProofContext
open ProofPrinting

(** Type of in-progress proof of [Prover] *)
type uproof = U_Unfinished of goal * proof_context | U_Finished of incproof

let raise_unproven goal =
  failwith $ Printf.sprintf "You haven't proven `%s` yet!" (string_of_goal goal)

let raise_unknown_hypothesis h = failwith $ Printf.sprintf "Hypothesis \"%s\" not in environment" h

let raise_finished () = failwith "Proof finished"

let raise_hypothesis_doesnt_match_goal h_name h_formula goal =
  failwith
  $ Printf.sprintf "Hypothesis%s is `%s`, but goal is `%s`"
      ( match h_name with
      | None   -> ""
      | Some h -> Printf.sprintf "\"%s\"" h )
      (string_of_formula h_formula) (string_of_formula goal)

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

let env'' = function
  | U_Finished _               -> raise_finished ()
  | U_Unfinished ((env, _), _) -> env

let intro h = function
  | U_Unfinished (((env, f) as goal), ctx) -> (
    match f with
    | F_Impl (f1, f2) ->
        let goal' = (env_add h f1 env, f2) in
        U_Unfinished (goal', PC_Intro (goal_to_judgement goal, ctx))
    | _               -> failwith $ Printf.sprintf "%s is not an implication" (string_of_formula f)
    )
  | U_Finished _ -> raise_finished ()

let axiom f env = PI_Axiom (goal_env_to_env env, f)

let hole f env = PI_Hole (env, f)

let apply' h h_proof h_name =
  let rec apply_impl_list env iproof = function
    | []                    -> iproof
    | F_Impl (h, g) :: rest ->
        apply_impl_list env (PI_Apply (goal_to_judgement (env, g), PI_Hole (env, h), iproof)) rest
    | _                     -> assert false
  in
  function
  | U_Finished _ -> raise_finished ()
  | U_Unfinished ((env, f), ctx) when f === h -> find_goal_in_ctx (h_proof env) ctx
  | U_Unfinished ((env, f), ctx) -> (
    match destruct_impl f h with
    | []    -> raise_hypothesis_doesnt_match_goal h_name h f
    | assms -> find_goal_in_proof ctx $ apply_impl_list env (h_proof env) assms )

let apply h = apply' h (hole h) None

let apply_thm iproof = apply' (label' iproof) (const iproof) None

let apply_assm h_name uproof =
  match List.assoc_opt h_name (env'' uproof) with
  | None   -> raise_unknown_hypothesis h_name
  | Some h -> apply' h (axiom h) (Some h_name) uproof

let ex_falso = function
  | U_Finished _                 -> raise_finished ()
  | U_Unfinished ((env, f), ctx) ->
      U_Unfinished ((env, F_Bot), PC_ExFalso ((goal_env_to_env env, f), ctx))

let qed = function
  | U_Unfinished ((env, F_Top), _) -> PI_Axiom (goal_env_to_env env, F_Top)
  | U_Unfinished (goal, _)         -> raise_unproven goal
  | U_Finished iproof              -> (
    match find_goal_in_proof PC_Root iproof with
    | U_Finished _           -> iproof
    | U_Unfinished (goal, _) -> raise_unproven goal )
