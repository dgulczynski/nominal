open Prelude
open Proof
open ProofCommon
open ProofException
open ProverGoal
open Types
open Zipper

(** Possibly incomplete proof with the same structure as [proof], but with _holes_.
    For ease of development it is exported here, but in future it will be abstract *)
type incproof =
  | PI_Proven of proof
  | PI_Hole of goal
  | PI_Intro of judgement * incproof
  | PI_Apply of judgement * incproof * incproof
  | PI_ConstrAnd of judgement * incproof * incproof
  | PI_ConstrAndElimL of judgement * incproof
  | PI_ConstrAndElimR of judgement * incproof
  | PI_SpecializeAtom of judgement * permuted_atom * incproof
  | PI_SpecializeTerm of judgement * term * incproof
  | PI_ExistsAtom of judgement * permuted_atom * incproof
  | PI_ExistsTerm of judgement * term * incproof
  | PI_Witness of judgement * incproof * string * incproof
  | PI_And of judgement * incproof list
  | PI_AndElim of judgement * incproof
  | PI_Or of judgement * incproof
  | PI_OrElim of judgement * incproof * incproof list
  | PI_Induction of judgement * var_binder * var_binder * incproof
  | PI_Equivalent of judgement * int * incproof
  | PI_SubstAtom of judgement * atom * permuted_atom * incproof
  | PI_SubstVar of judgement * var * term * incproof
  | PI_ExFalso of judgement * incproof

type proof_context =
  | PC_Root of judgement
  | PC_Intro of judgement * proof_context
  | PC_ApplyLeft of judgement * proof_context * incproof
  | PC_ApplyRight of judgement * incproof * proof_context
  | PC_ConstrAndLeft of judgement * proof_context * incproof
  | PC_ConstrAndRight of judgement * incproof * proof_context
  | PC_ConstrAndElimL of judgement * proof_context
  | PC_ConstrAndElimR of judgement * proof_context
  | PC_SpecializeAtom of judgement * permuted_atom * proof_context
  | PC_SpecializeTerm of judgement * term * proof_context
  | PC_WitnessExists of judgement * proof_context * string * incproof
  | PC_WitnessUsage of judgement * incproof * string * proof_context
  | PC_ExistsAtom of judgement * permuted_atom * proof_context
  | PC_ExistsTerm of judgement * term * proof_context
  | PC_And of judgement * incproof zipper * proof_context
  | PC_AndElim of judgement * proof_context
  | PC_Or of judgement * proof_context
  | PC_OrElim of judgement * proof_context * incproof list
  | PC_OrElimDisjunct of judgement * incproof * incproof zipper * proof_context
  | PC_Induction of judgement * var_binder * var_binder * proof_context
  | PC_Equivalent of judgement * int * proof_context
  | PC_SubstAtom of judgement * atom * permuted_atom * proof_context
  | PC_SubstVar of judgement * var * term * proof_context
  | PC_ExFalso of judgement * proof_context

let judgement' = function
  | PI_Proven proof -> judgement proof
  | PI_Hole goal -> to_judgement goal
  | PI_Intro (jgmt, _)
  | PI_Apply (jgmt, _, _)
  | PI_ConstrAnd (jgmt, _, _)
  | PI_ConstrAndElimL (jgmt, _)
  | PI_ConstrAndElimR (jgmt, _)
  | PI_SpecializeAtom (jgmt, _, _)
  | PI_SpecializeTerm (jgmt, _, _)
  | PI_ExistsAtom (jgmt, _, _)
  | PI_ExistsTerm (jgmt, _, _)
  | PI_Witness (jgmt, _, _, _)
  | PI_And (jgmt, _)
  | PI_AndElim (jgmt, _)
  | PI_Or (jgmt, _)
  | PI_OrElim (jgmt, _, _)
  | PI_Induction (jgmt, _, _, _)
  | PI_Equivalent (jgmt, _, _)
  | PI_SubstAtom (jgmt, _, _, _)
  | PI_SubstVar (jgmt, _, _, _)
  | PI_ExFalso (jgmt, _) -> jgmt

let env' = fst % judgement'

let label' = snd % judgement'

let rec hasHoles = function
  | PI_Proven _ -> false
  | PI_Hole _ -> true
  | PI_Intro (_, p)
  | PI_SpecializeAtom (_, _, p)
  | PI_SpecializeTerm (_, _, p)
  | PI_ExistsAtom (_, _, p)
  | PI_ExistsTerm (_, _, p)
  | PI_AndElim (_, p)
  | PI_ConstrAndElimL (_, p)
  | PI_ConstrAndElimR (_, p)
  | PI_Or (_, p)
  | PI_Induction (_, _, _, p)
  | PI_Equivalent (_, _, p)
  | PI_SubstAtom (_, _, _, p)
  | PI_SubstVar (_, _, _, p)
  | PI_ExFalso (_, p) -> hasHoles p
  | PI_Apply (_, l, r) | PI_Witness (_, l, _, r) | PI_ConstrAnd (_, l, r) -> hasHoles l || hasHoles r
  | PI_And (_, ps) -> List.exists hasHoles ps
  | PI_OrElim (_, p, ps) -> List.exists hasHoles (p :: ps)

let rec ctxHasHoles = function
  | PC_Intro (_, ctx)
  | PC_SpecializeAtom (_, _, ctx)
  | PC_SpecializeTerm (_, _, ctx)
  | PC_ExistsAtom (_, _, ctx)
  | PC_ExistsTerm (_, _, ctx)
  | PC_AndElim (_, ctx)
  | PC_ConstrAndElimL (_, ctx)
  | PC_ConstrAndElimR (_, ctx)
  | PC_Or (_, ctx)
  | PC_Induction (_, _, _, ctx)
  | PC_Equivalent (_, _, ctx)
  | PC_SubstAtom (_, _, _, ctx)
  | PC_SubstVar (_, _, _, ctx)
  | PC_ExFalso (_, ctx) -> ctxHasHoles ctx
  | PC_ApplyLeft (_, ctx, proof)
  | PC_WitnessExists (_, ctx, _, proof)
  | PC_ConstrAndLeft (_, ctx, proof)
  | PC_ApplyRight (_, proof, ctx)
  | PC_WitnessUsage (_, proof, _, ctx)
  | PC_ConstrAndRight (_, proof, ctx) -> ctxHasHoles ctx || hasHoles proof
  | PC_And (_, proofs, ctx) -> ctxHasHoles ctx || Zipper.exists hasHoles proofs
  | PC_OrElim (_, ctx, proofs) -> ctxHasHoles ctx || List.exists hasHoles proofs
  | PC_OrElimDisjunct (_, proof, proofs, ctx) -> ctxHasHoles ctx || hasHoles proof || Zipper.exists hasHoles proofs
  | PC_Root _ -> false

let rec root_judgement = function
  | PC_Root jgmt -> jgmt
  | PC_Intro (_, ctx)
  | PC_SpecializeAtom (_, _, ctx)
  | PC_SpecializeTerm (_, _, ctx)
  | PC_ExistsAtom (_, _, ctx)
  | PC_ExistsTerm (_, _, ctx)
  | PC_AndElim (_, ctx)
  | PC_ConstrAndElimL (_, ctx)
  | PC_ConstrAndElimR (_, ctx)
  | PC_Or (_, ctx)
  | PC_Induction (_, _, _, ctx)
  | PC_Equivalent (_, _, ctx)
  | PC_SubstAtom (_, _, _, ctx)
  | PC_SubstVar (_, _, _, ctx)
  | PC_ExFalso (_, ctx)
  | PC_ApplyLeft (_, ctx, _)
  | PC_WitnessExists (_, ctx, _, _)
  | PC_ConstrAndLeft (_, ctx, _)
  | PC_ApplyRight (_, _, ctx)
  | PC_WitnessUsage (_, _, _, ctx)
  | PC_ConstrAndRight (_, _, ctx)
  | PC_And (_, _, ctx)
  | PC_OrElim (_, ctx, _)
  | PC_OrElimDisjunct (_, _, _, ctx) -> root_judgement ctx

let proof_hole env f = PI_Hole (env, f)

let proven proof = PI_Proven proof

let proof_assumption env = proven % assumption env

let proof_constr env = proven % constr_i env

let rec normalize incproof =
  match incproof with
  | PI_Proven _ | PI_Hole _ -> incproof
  | PI_Intro (jgmt, conclusion_proof) -> proof_intro jgmt conclusion_proof
  | PI_ExFalso (jgmt, contradiction) -> proof_ex_falso jgmt contradiction
  | PI_Apply (jgmt, imp_proof, premise_proof) -> proof_apply jgmt imp_proof premise_proof
  | PI_ConstrAnd (jgmt, c_proof, f_proof) -> proof_constr_and jgmt c_proof f_proof
  | PI_ConstrAndElimL (jgmt, c_and_f_proof) -> proof_constr_and_elim_left jgmt c_and_f_proof
  | PI_ConstrAndElimR (jgmt, c_and_f_proof) -> proof_constr_and_elim_right jgmt c_and_f_proof
  | PI_SpecializeAtom (jgmt, a, universal_proof) -> proof_specialize_atom jgmt a universal_proof
  | PI_SpecializeTerm (jgmt, t, universal_proof) -> proof_specialize_term jgmt t universal_proof
  | PI_ExistsAtom (jgmt, witness, witness_proof) -> proof_exists_atom jgmt witness witness_proof
  | PI_ExistsTerm (jgmt, witness, witness_proof) -> proof_exists_term jgmt witness witness_proof
  | PI_Witness (jgmt, exists_proof, witness, usage_proof) -> proof_witness jgmt exists_proof witness usage_proof
  | PI_And (jgmt, proofs) -> proof_and jgmt proofs
  | PI_AndElim (jgmt, proof) -> proof_and_elim jgmt proof
  | PI_Or (jgmt, proof) -> proof_or jgmt proof
  | PI_OrElim (jgmt, or_proof, proofs) -> proof_or_elim jgmt or_proof proofs
  | PI_Induction (jgmt, x, y, proof) -> proof_induction jgmt x y proof
  | PI_Equivalent (jgmt, n, proof) -> proof_equivalent jgmt n proof
  | PI_SubstAtom (jgmt, a, b, proof) -> proof_subst_atom jgmt a b proof
  | PI_SubstVar (jgmt, x, t, proof) -> proof_subst_var jgmt x t proof

and normalize_many proofs =
  let aux proof =
    match normalize proof with
    | PI_Proven proof ->
      let left = List.cons $ proven proof and right = List.cons proof in
      Either.map ~left ~right
    | incproof ->
      let left = id and right = List.map proven in
      Either.left % List.cons incproof % Either.fold ~left ~right
  in
  List.fold_right aux proofs (Either.Right [])

and proof_intro jgmt conclusion_proof =
  match normalize conclusion_proof with
  | PI_Proven proof -> (
    match jgmt with
    | _, F_Impl (premise, _) -> proven $ imp_i premise proof
    | _, F_ForallAtom (a, _) -> proven $ forall_atom_i a proof
    | _, F_ForallTerm (x, _) -> proven $ forall_term_i x proof
    | _, F_ConstrImpl (c, _) -> proven $ constr_imp_i c proof
    | env, f -> raise $ not_an_implication f (ProofEnv.all_identifiers env) )
  | incproof -> PI_Intro (jgmt, incproof)

and proof_ex_falso jgmt contradiction =
  match normalize contradiction with
  | PI_Proven proof -> proven $ bot_e (snd jgmt) proof
  | incproof -> PI_ExFalso (jgmt, incproof)

and proof_apply jgmt imp_proof premise_proof =
  match (normalize imp_proof, normalize premise_proof) with
  | PI_Proven imp_proof, PI_Proven premise_proof -> proven (imp_e imp_proof premise_proof)
  | imp_proof, premise_proof -> PI_Apply (jgmt, imp_proof, premise_proof)

and proof_constr_and jgmt c_proof f_proof =
  match (normalize c_proof, normalize f_proof) with
  | PI_Proven c_proof, PI_Proven f_proof -> proven (constr_and_i c_proof f_proof)
  | c_proof, f_proof -> PI_ConstrAnd (jgmt, c_proof, f_proof)

and proof_specialize_atom jgmt (a : permuted_atom) universal_proof =
  match normalize universal_proof with
  | PI_Proven proof -> proven $ forall_atom_e a proof
  | incproof -> PI_SpecializeAtom (jgmt, a, incproof)

and proof_specialize_term jgmt t universal_proof =
  match normalize universal_proof with
  | PI_Proven proof -> proven $ forall_term_e t proof
  | incproof -> PI_SpecializeTerm (jgmt, t, incproof)

and proof_exists_atom jgmt witness witness_proof =
  match (snd jgmt, normalize witness_proof) with
  | F_ExistsAtom (a, f), PI_Proven witness_proof -> proven $ exists_atom_i a witness f witness_proof
  | _, incproof -> PI_ExistsAtom (jgmt, witness, incproof)

and proof_exists_term jgmt witness witness_proof =
  match (snd jgmt, normalize witness_proof) with
  | F_ExistsTerm (x, f), PI_Proven witness_proof -> proven $ exists_term_i x witness f witness_proof
  | _, incproof -> PI_ExistsTerm (jgmt, witness, incproof)

and proof_witness jgmt exists_proof witness usage_proof =
  match (normalize exists_proof, normalize usage_proof) with
  | PI_Proven exists_proof, PI_Proven usage_proof -> proven $ exist_e exists_proof witness usage_proof
  | exists_proof, usage_proof -> PI_Witness (jgmt, exists_proof, witness, usage_proof)

and proof_and jgmt proofs =
  match normalize_many proofs with
  | Either.Right proofs -> proven $ and_i proofs
  | Either.Left incproofs -> PI_And (jgmt, incproofs)

and proof_and_elim jgmt and_proof =
  match normalize and_proof with
  | PI_Proven proof -> proven $ and_e (snd jgmt) proof
  | incproof -> PI_AndElim (jgmt, incproof)

and proof_or jgmt proof =
  match normalize proof with
  | PI_Proven proof -> proven $ or_i (disjuncts $ snd jgmt) proof
  | incproof -> PI_Or (jgmt, incproof)

and proof_or_elim jgmt or_proof proofs =
  match normalize or_proof with
  | PI_Proven proof -> (
    match normalize_many proofs with
    | Either.Right proofs -> proven $ or_e proof proofs
    | Either.Left incproofs -> PI_OrElim (jgmt, proven proof, incproofs) )
  | incproof -> PI_OrElim (jgmt, incproof, proofs)

and proof_induction jgmt x y inductive_proof =
  match normalize inductive_proof with
  | PI_Proven proof -> proven $ induction_e x y proof
  | incproof -> PI_Induction (jgmt, x, y, incproof)

and proof_equivalent jgmt n proof =
  match normalize proof with
  | PI_Proven proof -> proven $ equivalent jgmt n proof
  | incproof -> PI_Equivalent (jgmt, n, incproof)

and proof_subst_atom jgmt a b proof =
  match normalize proof with
  | PI_Proven proof -> proven $ subst_atom a b jgmt proof
  | incproof -> PI_SubstAtom (jgmt, a, b, incproof)

and proof_subst_var jgmt x t proof =
  match normalize proof with
  | PI_Proven proof -> proven $ subst_var x t jgmt proof
  | incproof -> PI_SubstVar (jgmt, x, t, incproof)

and proof_constr_and_elim_left jgmt c_and_f_proof =
  match normalize c_and_f_proof with
  | PI_Proven proof -> proven $ constr_and_e_left proof
  | incproof -> PI_ConstrAndElimL (jgmt, incproof)

and proof_constr_and_elim_right jgmt c_and_f_proof =
  match normalize c_and_f_proof with
  | PI_Proven proof -> proven $ constr_and_e_right proof
  | incproof -> PI_ConstrAndElimL (jgmt, incproof)

let proof_step n p =
  let env, f = judgement' p in
  let env', _, f' = ProofEquiv.computeWHNF env n f in
  PI_Equivalent ((env', f'), n, p)

let proof_case map_proof map_incproof incproof =
  match normalize incproof with
  | PI_Proven proof -> map_proof proof
  | incproof -> map_incproof incproof

let incproof_to_proof =
  let on_incomplete _ = raise hole_in_proof in
  proof_case id on_incomplete

let is_proven = function
  | PI_Proven _ -> true
  | _ -> false

let rec find_hole_in_proof context = function
  | PI_Intro (jgmt, incproof) -> find_hole_in_proof (PC_Intro (jgmt, context)) incproof
  | PI_ExFalso (jgmt, incproof) -> find_hole_in_proof (PC_ExFalso (jgmt, context)) incproof
  | PI_SpecializeAtom (jgmt, a, incproof) -> find_hole_in_proof (PC_SpecializeAtom (jgmt, a, context)) incproof
  | PI_SpecializeTerm (jgmt, t, incproof) -> find_hole_in_proof (PC_SpecializeTerm (jgmt, t, context)) incproof
  | PI_Apply (jgmt, lproof, rproof) when hasHoles lproof ->
    find_hole_in_proof (PC_ApplyLeft (jgmt, context, rproof)) lproof
  | PI_Apply (jgmt, lproof, rproof) when hasHoles rproof ->
    find_hole_in_proof (PC_ApplyRight (jgmt, lproof, context)) rproof
  | PI_Apply _ as incproof -> Either.Left (incproof_to_proof incproof, context)
  | PI_ConstrAnd (jgmt, lproof, rproof) when hasHoles lproof ->
    find_hole_in_proof (PC_ConstrAndLeft (jgmt, context, rproof)) lproof
  | PI_ConstrAnd (jgmt, lproof, rproof) when hasHoles rproof ->
    find_hole_in_proof (PC_ConstrAndRight (jgmt, lproof, context)) rproof
  | PI_ConstrAnd _ as incproof -> Either.Left (incproof_to_proof incproof, context)
  | PI_ConstrAndElimL (jgmt, c_and_proof) -> find_hole_in_proof (PC_ConstrAndElimL (jgmt, context)) c_and_proof
  | PI_ConstrAndElimR (jgmt, c_and_proof) -> find_hole_in_proof (PC_ConstrAndElimR (jgmt, context)) c_and_proof
  | PI_Witness (jgmt, exists_proof, witness, usage_proof) when hasHoles exists_proof ->
    find_hole_in_proof (PC_WitnessExists (jgmt, context, witness, usage_proof)) exists_proof
  | PI_Witness (jgmt, exists_proof, witness, usage_proof) when hasHoles usage_proof ->
    find_hole_in_proof (PC_WitnessUsage (jgmt, exists_proof, witness, context)) usage_proof
  | PI_Witness _ as incproof -> Either.Left (incproof_to_proof incproof, context)
  | PI_ExistsAtom (jgmt, witness, incproof) -> find_hole_in_proof (PC_ExistsAtom (jgmt, witness, context)) incproof
  | PI_ExistsTerm (jgmt, witness, incproof) -> find_hole_in_proof (PC_ExistsTerm (jgmt, witness, context)) incproof
  | PI_Proven proof -> Either.Left (proof, context)
  | PI_Hole goal -> Either.Right (goal, context)
  | PI_AndElim (jgmt, proof) -> find_hole_in_proof (PC_AndElim (jgmt, context)) proof
  | PI_Or (jgmt, proof) -> find_hole_in_proof (PC_Or (jgmt, context)) proof
  | PI_And (jgmt, proofs) ->
    let proof_from proofs = (incproof_to_proof $ proof_and jgmt proofs, context) in
    let context_from zipper = PC_And (jgmt, zipper, context) in
    find_hole_in_many proofs proof_from context_from
  | PI_OrElim (jgmt, or_proof, proofs) ->
    if hasHoles or_proof then
      find_hole_in_proof (PC_OrElim (jgmt, context, proofs)) or_proof
    else
      let proof_from proofs = (incproof_to_proof $ proof_or_elim jgmt or_proof proofs, context) in
      let context_from zipper = PC_OrElimDisjunct (jgmt, or_proof, zipper, context) in
      find_hole_in_many proofs proof_from context_from
  | PI_Induction (jgmt, x, y, incproof) -> find_hole_in_proof (PC_Induction (jgmt, x, y, context)) incproof
  | PI_Equivalent (jgmt, n, incproof) -> find_hole_in_proof (PC_Equivalent (jgmt, n, context)) incproof
  | PI_SubstAtom (jgmt, a, b, incproof) -> find_hole_in_proof (PC_SubstAtom (jgmt, a, b, context)) incproof
  | PI_SubstVar (jgmt, x, t, incproof) -> find_hole_in_proof (PC_SubstVar (jgmt, x, t, context)) incproof

and find_hole_in_many proofs proof_from context_from =
  let proofs = List.map normalize proofs in
  match extract_next (not % is_proven) (Zipper.from_list proofs) with
  | None -> Either.Left (proof_from proofs)
  | Some (incproof, zipper) -> find_hole_in_proof (context_from zipper) incproof

(** [meld proof ctx] rebuilds the proof from context *)
let rec meld incproof = function
  | PC_Root _ -> proof_case proven id incproof
  | PC_Intro (jgmt, ctx) -> meld (proof_intro jgmt incproof) ctx
  | PC_ApplyRight (jgmt, lproof, rctx) -> meld (proof_apply jgmt lproof incproof) rctx
  | PC_ApplyLeft (jgmt, lctx, rproof) -> meld (proof_apply jgmt incproof rproof) lctx
  | PC_ConstrAndRight (jgmt, lproof, rctx) -> meld (proof_constr_and jgmt lproof incproof) rctx
  | PC_ConstrAndLeft (jgmt, lctx, rproof) -> meld (proof_constr_and jgmt incproof rproof) lctx
  | PC_ConstrAndElimR (jgmt, ctx) -> meld (proof_constr_and_elim_left jgmt incproof) ctx
  | PC_ConstrAndElimL (jgmt, ctx) -> meld (proof_constr_and_elim_right jgmt incproof) ctx
  | PC_SpecializeAtom (jgmt, a, ctx) -> meld (proof_specialize_atom jgmt a incproof) ctx
  | PC_SpecializeTerm (jgmt, t, ctx) -> meld (proof_specialize_term jgmt t incproof) ctx
  | PC_ExistsAtom (jgmt, witness, ctx) -> meld (proof_exists_atom jgmt witness incproof) ctx
  | PC_ExistsTerm (jgmt, witness, ctx) -> meld (proof_exists_term jgmt witness incproof) ctx
  | PC_WitnessExists (jgmt, ctx, witness, usage_proof) -> meld (proof_witness jgmt incproof witness usage_proof) ctx
  | PC_WitnessUsage (jgmt, exists_proof, witness, ctx) -> meld (proof_witness jgmt exists_proof witness incproof) ctx
  | PC_And (jgmt, proofs, ctx) ->
    let proofs = Zipper.to_list $ Zipper.insert incproof proofs in
    meld (proof_and jgmt proofs) ctx
  | PC_AndElim (jgmt, ctx) -> meld (proof_and_elim jgmt incproof) ctx
  | PC_Or (jgmt, ctx) -> meld (proof_or jgmt incproof) ctx
  | PC_OrElim (jgmt, ctx, proofs) -> meld (proof_or_elim jgmt incproof proofs) ctx
  | PC_OrElimDisjunct (jgmt, or_proof, proofs, ctx) ->
    let proofs = Zipper.to_list $ Zipper.insert incproof proofs in
    meld (proof_or_elim jgmt or_proof proofs) ctx
  | PC_Induction (jgmt, x, y, ctx) -> meld (proof_induction jgmt x y incproof) ctx
  | PC_Equivalent (jgmt, n, ctx) -> meld (proof_equivalent jgmt n incproof) ctx
  | PC_SubstAtom (jgmt, a, b, ctx) -> meld (proof_subst_atom jgmt a b incproof) ctx
  | PC_SubstVar (jgmt, x, t, ctx) -> meld (proof_subst_var jgmt x t incproof) ctx
  | PC_ExFalso (jgmt, ctx) -> meld (proof_ex_falso jgmt incproof) ctx
