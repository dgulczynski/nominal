open Common
open IncProof
open Proof
open ProofCommon
open ProofEnv
open ProofEquiv
open ProofException
open ProverGoal
open Printing
open Substitution
open Types

(** Type of in-progress proof of [Prover] *)
type prover_state = S_Unfinished of {goal: goal; context: proof_context} | S_Finished of proof

(** "Smart" constructor for proof state.
    Notice that there is no constructor of [S_Finished] state available for the user, as only the [ProverInternals] can finish a proof. *)
let unfinished goal context = S_Unfinished {goal; context}

let finished proof = S_Finished proof

type tactic = prover_state -> prover_state

let unproven goal (env, f) =
  let exn =
    Printf.sprintf "Proof of `%s`: You haven't proven `%s` yet!"
      (string_of_formula_in_env (all_identifiers $ env) f)
      (string_of_goal goal)
  in
  ProofException exn

(** Helper function that traverses [incproof] and returns [S_Unfinished {goal; context}] of a first found hole 
    (where [context] is its context in [incproof]) or [S_Finished incproof] if [incproof] has no holes *)
let rec find_goal_in_proof context incproof =
  match find_hole_in_proof context incproof with
  | Either.Left (proof, context) -> find_goal_in_ctx (proven proof) context
  | Either.Right (goal, context) -> unfinished goal context

(** Helper functions that given [incproof] and its [context] builds appropriate [state] *)
and find_goal_in_ctx incproof = function
  | PC_Root _ as ctx -> proof_case finished (find_goal_in_proof ctx) incproof
  | PC_Intro (jgmt, ctx) -> find_goal_in_ctx (proof_intro jgmt incproof) ctx
  | PC_ApplyRight (jgmt, lproof, rctx) -> find_goal_in_ctx (proof_apply jgmt lproof incproof) rctx
  | PC_ApplyLeft (jgmt, lctx, rproof) -> find_goal_in_ctx (proof_apply jgmt incproof rproof) lctx
  | PC_ConstrAndRight (jgmt, lproof, rctx) -> find_goal_in_ctx (proof_constr_and jgmt lproof incproof) rctx
  | PC_ConstrAndLeft (jgmt, lctx, rproof) -> find_goal_in_ctx (proof_constr_and jgmt incproof rproof) lctx
  | PC_ConstrAndElimR (jgmt, ctx) -> find_goal_in_ctx (proof_constr_and_elim_left jgmt incproof) ctx
  | PC_ConstrAndElimL (jgmt, ctx) -> find_goal_in_ctx (proof_constr_and_elim_right jgmt incproof) ctx
  | PC_SpecializeAtom (jgmt, a, ctx) -> find_goal_in_ctx (proof_specialize_atom jgmt a incproof) ctx
  | PC_SpecializeTerm (jgmt, t, ctx) -> find_goal_in_ctx (proof_specialize_term jgmt t incproof) ctx
  | PC_ExistsAtom (jgmt, witness, ctx) -> find_goal_in_ctx (proof_exists_atom jgmt witness incproof) ctx
  | PC_ExistsTerm (jgmt, witness, ctx) -> find_goal_in_ctx (proof_exists_term jgmt witness incproof) ctx
  | PC_WitnessExists (jgmt, ctx, witness, usage_proof) ->
      find_goal_in_ctx (proof_witness jgmt incproof witness usage_proof) ctx
  | PC_WitnessUsage (jgmt, exists_proof, witness, ctx) ->
      find_goal_in_ctx (proof_witness jgmt exists_proof witness incproof) ctx
  | PC_And (jgmt, proofs, ctx) ->
      let proofs = Zipper.to_list $ Zipper.insert incproof proofs in
      find_goal_in_ctx (proof_and jgmt proofs) ctx
  | PC_AndElim (jgmt, ctx) -> find_goal_in_ctx (proof_and_elim jgmt incproof) ctx
  | PC_Or (jgmt, ctx) -> find_goal_in_ctx (proof_or jgmt incproof) ctx
  | PC_OrElim (jgmt, ctx, proofs) -> find_goal_in_ctx (proof_or_elim jgmt incproof proofs) ctx
  | PC_OrElimDiscjunt (jgmt, or_proof, proofs, ctx) ->
      let proofs = Zipper.to_list $ Zipper.insert incproof proofs in
      find_goal_in_ctx (proof_or_elim jgmt or_proof proofs) ctx
  | PC_Induction (jgmt, x, y, ctx) -> find_goal_in_ctx (proof_induction jgmt x y incproof) ctx
  | PC_Equivalent (jgmt, n, ctx) -> find_goal_in_ctx (proof_equivalent jgmt n incproof) ctx
  | PC_SubstAtom (jgmt, a, b, ctx) -> find_goal_in_ctx (proof_subst_atom jgmt a b incproof) ctx
  | PC_SubstVar (jgmt, x, t, ctx) -> find_goal_in_ctx (proof_subst_var jgmt x t incproof) ctx
  | PC_ExFalso (jgmt, ctx) -> find_goal_in_ctx (proof_ex_falso jgmt incproof) ctx

(** [destruct_impl c f] is
    [Some [f1 => f2 => ... fn => c; f2 => ... fn => c; ...; fn => c]] if [f = f1 => f2 => ... => fn => c]
    and [[]] otherwise *)
let destruct_impl env c f =
  let rec aux f =
    match conclusion f with
    | f2 when f2 === c <| env -> [f]
    | f2 -> f :: aux f2
  in
  try aux f with ProofException _ -> []

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

let name_taken name =
  let exn = Printf.sprintf "Name `%s` is already taken" name in
  ProofException exn

let check_fresh env name =
  let identifiers = identifiers env in
  let check (Bind (x_name, _)) = if name <> x_name then () else raise $ name_taken x_name in
  List.iter check identifiers

let intro_named name state =
  let env, f = goal state in
  let _ = check_fresh env name in
  match f with
  | F_Impl (f1, f2)     ->
      let ctx = PC_Intro (to_judgement (env, f), context state) in
      unfinished (env |> add_assumption (name, f1), f2) ctx
  | F_ForallAtom _ as f ->
      let A_Bind (_, a), f = instantiate_atom f in
      let a_bind = A_Bind (name, a) in
      let ctx = PC_Intro (to_judgement (env, F_ForallAtom (a_bind, f)), context state) in
      unfinished (env |> add_atom a_bind, f) ctx
  | F_ForallTerm _ as f ->
      let V_Bind (_, x), f = instantiate_var f in
      let x_bind = V_Bind (name, x) in
      let ctx = PC_Intro (to_judgement (env, F_ForallTerm (x_bind, f)), context state) in
      unfinished (env |> add_var x_bind, f) ctx
  | _                   -> raise $ not_an_implication f

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
  | S_Unfinished {goal= env, f; context} when f === h <| env -> find_goal_in_ctx h_proof context
  | S_Unfinished {goal= env, f; context} -> (
    match destruct_impl env f h with
    | []    -> raise $ hypothesis_goal_mismatch h_name h f
    | assms -> find_goal_in_proof context $ apply_impl_list env h_proof assms )

let finish = function
  | S_Unfinished {goal; context} -> raise % unproven goal $ root_judgement context
  | S_Finished proof             -> proof

let pp_print_state fmt = function
  | S_Unfinished {goal; _} -> pp_print_goal fmt goal
  | S_Finished _           -> Format.pp_print_string fmt "Finished"
