open Permutation

type permuted_identifier = (string, string) permuted

type pterm =
  | PT_Identifier of permuted_identifier
  | PT_Lam of permuted_identifier * pterm
  | PT_App of pterm * pterm
  | PT_Permuted of permuted_pterm

and permuted_pterm = (string, pterm) permuted

type pconstr =
  | PC_Fresh of string * pterm
  | PC_Eq of pterm * pterm
  | PC_Shape of pterm * pterm
  | PC_Subshape of pterm * pterm
  | PC_AtomNeq of permuted_identifier * permuted_identifier
  | PC_Symbol of pterm

type pkind =
  | PK_Prop
  | PK_ForallAtom of string * pkind
  | PK_ForallTerm of string * pkind
  | PK_Constr of pconstr * pkind
  | PK_Arrow of pkind * pkind

type pformula =
  | PF_Bot
  | PF_Top
  | PF_Constr of pconstr
  | PF_And of (string * pformula) list
  | PF_Or of (string * pformula) list
  | PF_Impl of pformula * pformula
  | PF_ForallProp of string * pkind * pformula
  | PF_ForallTerm of string * pformula
  | PF_ForallAtom of string * pformula
  | PF_ExistsProp of string * pkind * pformula
  | PF_ExistsTerm of string * pformula
  | PF_ExistsAtom of string * pformula
  | PF_ConstrAnd of pconstr * pformula
  | PF_ConstrImpl of pconstr * pformula
  | PF_Var of string
  | PF_Fun of string * pkind * pformula
  | PF_FunAtom of string * pformula
  | PF_FunTerm of string * pformula
  | PF_AppIdentfier of pformula * string
  | PF_App of pformula * pformula
  | PF_AppAtom of pformula * permuted_identifier
  | PF_AppTerm of pformula * pterm
  | PF_Fix of string * string * pkind * pformula

type pquantifier_kind = PQ_Atom | PQ_Term | PQ_Kind of pkind
