open IncProof
open Proof

type proof_context =
  | PC_Root
  | PC_Intro      of judgement * proof_context
  | PC_ApplyLeft  of judgement * proof_context * incproof
  | PC_ApplyRight of judgement * incproof * proof_context
  | PC_ExFalso    of judgement * proof_context

let rec ctxHasHoles = function
  | PC_Intro (_, ctx)               -> ctxHasHoles ctx
  | PC_ExFalso (_, ctx)             -> ctxHasHoles ctx
  | PC_ApplyLeft (_, lctx, rproof)  -> ctxHasHoles lctx || hasHoles rproof
  | PC_ApplyRight (_, lproof, rctx) -> ctxHasHoles rctx || hasHoles lproof
  | PC_Root                         -> false
