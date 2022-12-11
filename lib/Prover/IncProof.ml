open Common
open Proof
open ProofException
open ProverGoal
open ProofCommon

(** Possibly incomplete proof with the same structure as [proof], but with _holes_. 
    For ease of development it is exported here, but in future it will be abstract *)
type incproof =
  | PI_Proven  of proof
  | PI_Hole    of goal
  | PI_Intro   of judgement * incproof
  | PI_Apply   of judgement * incproof * incproof
  | PI_ExFalso of judgement * incproof

type proof_context =
  | PC_Root
  | PC_Intro      of judgement * proof_context
  | PC_ApplyLeft  of judgement * proof_context * incproof
  | PC_ApplyRight of judgement * incproof * proof_context
  | PC_ExFalso    of judgement * proof_context

let judgement' = function
  | PI_Proven proof -> judgement proof
  | PI_Hole goal -> to_judgement goal
  | PI_Intro (jgmt, _) | PI_Apply (jgmt, _, _) | PI_ExFalso (jgmt, _) -> jgmt

let env' = fst % judgement'

let label' = snd % judgement'

let rec hasHoles = function
  | PI_Proven _        -> false
  | PI_Hole _          -> true
  | PI_Intro (_, p)    -> hasHoles p
  | PI_ExFalso (_, p)  -> hasHoles p
  | PI_Apply (_, l, r) -> hasHoles l || hasHoles r

let rec ctxHasHoles = function
  | PC_Intro (_, ctx)               -> ctxHasHoles ctx
  | PC_ExFalso (_, ctx)             -> ctxHasHoles ctx
  | PC_ApplyLeft (_, lctx, rproof)  -> ctxHasHoles lctx || hasHoles rproof
  | PC_ApplyRight (_, lproof, rctx) -> ctxHasHoles rctx || hasHoles lproof
  | PC_Root                         -> false

let proof_hole env f = PI_Hole (env, f)

let proven proof = PI_Proven proof

let proof_axiom env = proven % by_assumption (ProofEnv.identifiers env)

let rec normalize incproof =
  match incproof with
  | PI_Proven _ | PI_Hole _ -> incproof
  | PI_Intro (jgmt, conclusion_proof) -> proof_intro jgmt conclusion_proof
  | PI_ExFalso (jgmt, contradiction) -> proof_ex_falso jgmt contradiction
  | PI_Apply (jgmt, imp_proof, premise_proof) -> proof_apply jgmt imp_proof premise_proof

and proof_intro jgmt conclusion_proof =
  match normalize conclusion_proof with
  | PI_Proven proof -> proven (imp_i (premise $ snd jgmt) proof)
  | incproof        -> PI_Intro (jgmt, incproof)

and proof_ex_falso jgmt contradiction =
  match normalize contradiction with
  | PI_Proven proof -> proven (bot_e (snd jgmt) proof)
  | incproof        -> PI_ExFalso (jgmt, incproof)

and proof_apply jgmt imp_proof premise_proof =
  match (normalize imp_proof, normalize premise_proof) with
  | PI_Proven imp_proof, PI_Proven premise_proof -> proven (imp_e imp_proof premise_proof)
  | imp_proof, premise_proof -> PI_Apply (jgmt, imp_proof, premise_proof)

let proof_case map_proof map_incproof incproof =
  match normalize incproof with
  | PI_Proven proof -> map_proof proof
  | incproof        -> map_incproof incproof

let incproof_to_proof =
  let on_incomplete _ = raise hole_in_proof in
  proof_case id on_incomplete

let rec find_hole_in_proof context = function
  | PI_Intro (jgmt, incproof) -> find_hole_in_proof (PC_Intro (jgmt, context)) incproof
  | PI_ExFalso (jgmt, incproof) -> find_hole_in_proof (PC_ExFalso (jgmt, context)) incproof
  | PI_Apply (jgmt, lproof, rproof) when hasHoles lproof ->
      find_hole_in_proof (PC_ApplyLeft (jgmt, context, rproof)) lproof
  | PI_Apply (jgmt, lproof, rproof) when hasHoles rproof ->
      find_hole_in_proof (PC_ApplyRight (jgmt, lproof, context)) rproof
  | PI_Apply _ as incproof -> Either.Left (incproof_to_proof incproof, context)
  | PI_Proven proof -> Either.Left (proof, context)
  | PI_Hole goal -> Either.Right (goal, context)