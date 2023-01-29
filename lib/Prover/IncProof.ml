open Common
open Proof
open ProofException
open ProverGoal
open ProofCommon
open Types

(** Possibly incomplete proof with the same structure as [proof], but with _holes_. 
    For ease of development it is exported here, but in future it will be abstract *)
type incproof =
  | PI_Proven         of proof
  | PI_Hole           of goal
  | PI_Intro          of judgement * incproof
  | PI_Apply          of judgement * incproof * incproof
  | PI_ConstrIntro    of judgement * incproof
  | PI_SpecializeAtom of judgement * atom * incproof
  | PI_SpecializeTerm of judgement * term * incproof
  | PI_ExistsAtom     of judgement * atom * incproof
  | PI_ExistsTerm     of judgement * term * incproof
  | PI_Witness        of judgement * incproof * incproof
  | PI_ExFalso        of judgement * incproof

type proof_context =
  | PC_Root
  | PC_Intro          of judgement * proof_context
  | PC_ApplyLeft      of judgement * proof_context * incproof
  | PC_ApplyRight     of judgement * incproof * proof_context
  | PC_ConstrIntro    of judgement * proof_context
  | PC_SpecializeAtom of judgement * atom * proof_context
  | PC_SpecializeTerm of judgement * term * proof_context
  | PC_WitnessExists  of judgement * proof_context * incproof
  | PC_WitnessUsage   of judgement * incproof * proof_context
  | PC_ExistsAtom     of judgement * atom * proof_context
  | PC_ExistsTerm     of judgement * term * proof_context
  | PC_ExFalso        of judgement * proof_context

let judgement' = function
  | PI_Proven proof -> judgement proof
  | PI_Hole goal -> to_judgement goal
  | PI_Intro (jgmt, _)
  | PI_ConstrIntro (jgmt, _)
  | PI_Apply (jgmt, _, _)
  | PI_SpecializeAtom (jgmt, _, _)
  | PI_SpecializeTerm (jgmt, _, _)
  | PI_ExistsAtom (jgmt, _, _)
  | PI_ExistsTerm (jgmt, _, _)
  | PI_Witness (jgmt, _, _)
  | PI_ExFalso (jgmt, _) -> jgmt

let env' = fst % judgement'

let label' = snd % judgement'

let rec hasHoles = function
  | PI_Proven _ -> false
  | PI_Hole _ -> true
  | PI_Intro (_, p)
  | PI_ConstrIntro (_, p)
  | PI_SpecializeAtom (_, _, p)
  | PI_SpecializeTerm (_, _, p)
  | PI_ExistsAtom (_, _, p)
  | PI_ExistsTerm (_, _, p)
  | PI_ExFalso (_, p) -> hasHoles p
  | PI_Apply (_, l, r) | PI_Witness (_, l, r) -> hasHoles l || hasHoles r

let rec ctxHasHoles = function
  | PC_Intro (_, ctx)
  | PC_ConstrIntro (_, ctx)
  | PC_SpecializeAtom (_, _, ctx)
  | PC_SpecializeTerm (_, _, ctx)
  | PC_ExistsAtom (_, _, ctx)
  | PC_ExistsTerm (_, _, ctx)
  | PC_ExFalso (_, ctx) -> ctxHasHoles ctx
  | PC_ApplyLeft (_, lctx, rproof) | PC_WitnessExists (_, lctx, rproof) ->
      ctxHasHoles lctx || hasHoles rproof
  | PC_ApplyRight (_, lproof, rctx) | PC_WitnessUsage (_, lproof, rctx) ->
      ctxHasHoles rctx || hasHoles lproof
  | PC_Root -> false

let proof_hole env f = PI_Hole (env, f)

let proven proof = PI_Proven proof

let proof_axiom env = proven % axiom (ProofEnv.identifiers env)

let proof_constr env = proven % constr_i env

let rec normalize incproof =
  match incproof with
  | PI_Proven _ | PI_Hole _ -> incproof
  | PI_Intro (jgmt, conclusion_proof) -> proof_intro jgmt conclusion_proof
  | PI_ConstrIntro (jgmt, conclusion_proof) -> proof_constr_intro jgmt conclusion_proof
  | PI_ExFalso (jgmt, contradiction) -> proof_ex_falso jgmt contradiction
  | PI_Apply (jgmt, imp_proof, premise_proof) -> proof_apply jgmt imp_proof premise_proof
  | PI_SpecializeAtom (jgmt, a, universal_proof) -> proof_specialize_atom jgmt a universal_proof
  | PI_SpecializeTerm (jgmt, t, universal_proof) -> proof_specialize_term jgmt t universal_proof
  | PI_ExistsAtom (jgmt, witness, witness_proof) -> proof_exists_atom jgmt witness witness_proof
  | PI_ExistsTerm (jgmt, witness, witness_proof) -> proof_exists_term jgmt witness witness_proof
  | PI_Witness (jgmt, exists_proof, usage_proof) -> proof_witness jgmt exists_proof usage_proof

and proof_intro jgmt conclusion_proof =
  match normalize conclusion_proof with
  | PI_Proven proof -> (
    match snd jgmt with
    | F_Impl (premise, _) -> proven $ imp_i premise proof
    | F_ForallAtom (a, _) -> proven $ forall_atom_i a proof
    | f                   -> raise $ not_an_implication f )
  | incproof        -> PI_Intro (jgmt, incproof)

and proof_constr_intro jgmt conclusion_proof =
  match normalize conclusion_proof with
  | PI_Proven proof -> proven $ constr_imp_i (to_constr % premise $ snd jgmt) proof
  | incproof        -> PI_ConstrIntro (jgmt, incproof)

and proof_ex_falso jgmt contradiction =
  match normalize contradiction with
  | PI_Proven proof -> proven $ bot_e (snd jgmt) proof
  | incproof        -> PI_ExFalso (jgmt, incproof)

and proof_apply jgmt imp_proof premise_proof =
  match (normalize imp_proof, normalize premise_proof) with
  | PI_Proven imp_proof, PI_Proven premise_proof -> proven (imp_e imp_proof premise_proof)
  | imp_proof, premise_proof -> PI_Apply (jgmt, imp_proof, premise_proof)

and proof_specialize_atom jgmt a universal_proof =
  match normalize universal_proof with
  | PI_Proven proof -> proven $ forall_atom_e a proof
  | incproof        -> PI_SpecializeAtom (jgmt, a, incproof)

and proof_specialize_term jgmt t universal_proof =
  match normalize universal_proof with
  | PI_Proven proof -> proven $ forall_term_e t proof
  | incproof        -> PI_SpecializeTerm (jgmt, t, incproof)

and proof_exists_atom jgmt witness witness_proof =
  match (snd jgmt, normalize witness_proof) with
  | F_ExistsAtom (a, f), PI_Proven witness_proof -> proven $ exists_atom_i a witness f witness_proof
  | _, incproof -> PI_ExistsAtom (jgmt, witness, incproof)

and proof_exists_term jgmt witness witness_proof =
  match (snd jgmt, normalize witness_proof) with
  | F_ExistsTerm (x, f), PI_Proven witness_proof -> proven $ exists_term_i x witness f witness_proof
  | _, incproof -> PI_ExistsTerm (jgmt, witness, incproof)

and proof_witness jgmt exists_proof usage_proof =
  match (normalize exists_proof, normalize usage_proof) with
  | PI_Proven exists_proof, PI_Proven usage_proof -> proven $ exists_atom_e exists_proof usage_proof
  | exists_proof, usage_proof -> PI_Witness (jgmt, exists_proof, usage_proof)

let proof_case map_proof map_incproof incproof =
  match normalize incproof with
  | PI_Proven proof -> map_proof proof
  | incproof        -> map_incproof incproof

let incproof_to_proof =
  let on_incomplete _ = raise hole_in_proof in
  proof_case id on_incomplete

let rec find_hole_in_proof context = function
  | PI_Intro (jgmt, incproof) -> find_hole_in_proof (PC_Intro (jgmt, context)) incproof
  | PI_ConstrIntro (jgmt, incproof) -> find_hole_in_proof (PC_ConstrIntro (jgmt, context)) incproof
  | PI_ExFalso (jgmt, incproof) -> find_hole_in_proof (PC_ExFalso (jgmt, context)) incproof
  | PI_SpecializeAtom (jgmt, a, incproof) ->
      find_hole_in_proof (PC_SpecializeAtom (jgmt, a, context)) incproof
  | PI_SpecializeTerm (jgmt, t, incproof) ->
      find_hole_in_proof (PC_SpecializeTerm (jgmt, t, context)) incproof
  | PI_Apply (jgmt, lproof, rproof) when hasHoles lproof ->
      find_hole_in_proof (PC_ApplyLeft (jgmt, context, rproof)) lproof
  | PI_Apply (jgmt, lproof, rproof) when hasHoles rproof ->
      find_hole_in_proof (PC_ApplyRight (jgmt, lproof, context)) rproof
  | PI_Apply _ as incproof -> Either.Left (incproof_to_proof incproof, context)
  | PI_Witness (jgmt, exists_proof, usage_proof) when hasHoles exists_proof ->
      find_hole_in_proof (PC_WitnessExists (jgmt, context, usage_proof)) exists_proof
  | PI_Witness (jgmt, exists_proof, usage_proof) when hasHoles usage_proof ->
      find_hole_in_proof (PC_WitnessUsage (jgmt, exists_proof, context)) usage_proof
  | PI_Witness _ as incproof -> Either.Left (incproof_to_proof incproof, context)
  | PI_ExistsAtom (jgmt, witness, incproof) ->
      find_hole_in_proof (PC_ExistsAtom (jgmt, witness, context)) incproof
  | PI_ExistsTerm (jgmt, witness, incproof) ->
      find_hole_in_proof (PC_ExistsTerm (jgmt, witness, context)) incproof
  | PI_Proven proof -> Either.Left (proof, context)
  | PI_Hole goal -> Either.Right (goal, context)
