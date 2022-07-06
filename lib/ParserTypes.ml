open Types
open Permutation

type permuted_identifier = (atom, string) permuted

type pterm =
  | PT_Identifier of permuted_identifier
  | PT_Lam        of atom * pterm
  | PT_App        of pterm * pterm

type pconstr =
  | PC_Fresh    of atom * pterm
  | PC_Eq       of pterm * pterm
  | PC_Shape    of pterm * pterm
  | PC_Subshape of pterm * pterm
  | PC_AtomNeq  of permuted_atom * permuted_atom

type pkind =
  | PK_Prop
  | PK_Forall of string * pkind
  | PK_Constr of pconstr * pkind
  | PK_Arrow  of pkind * pkind

type pformula =
  | PF_Bot
  | PF_Top
  | PF_Constr       of pconstr
  | PF_And          of pformula list
  | PF_Or           of pformula list
  | PF_Impl         of pformula * pformula
  | PF_ForallTerm   of string * pformula
  | PF_ForallAtom   of string * pformula
  | PF_ExistsTerm   of string * pformula
  | PF_ExistsAtom   of string * pformula
  | PF_ConstrAnd    of pconstr * pformula
  | PF_ConstrImpl   of pconstr * pformula
  | PF_Var          of string
  | PF_Fun          of string * pkind * pformula
  | PF_FunAtom      of string * pformula
  | PF_FunTerm      of string * pformula
  | PF_AppIdentfier of pformula * string
  | PF_App          of pformula * pformula
  | PF_AppTerm      of pformula * pterm
  | PF_Fix          of string * string * pkind * pformula
