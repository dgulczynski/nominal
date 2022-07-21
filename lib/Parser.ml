open Angstrom
open Types
open Common
open Permutation
open ParserTypes
open ParserCommon

let term : pterm t = ParserTerm.term

let constr : pconstr t = ParserConstr.constr

let kind : pkind t = ParserKind.kind

let formula : pformula t = ParserFormula.formula

let parse = ParserCommon.parse

type pidentifier_kind = PI_Atom | PI_Var | PI_FVar

type pidentifier_env = (string * pidentifier_kind) list

let unbound_variable x = ParserException (Printf.sprintf "Unbound variable %s" x)

let wrong_use expected x actual = ParserException (Printf.sprintf "%s %s used %s" expected x actual)

let rec idperm_to_aperm p =
  let idswap_to_aswap ({perm= p1; symb= a1}, {perm= p2; symb= a2}) =
    ({perm= idperm_to_aperm p1; symb= A a1}, {perm= idperm_to_aperm p2; symb= A a2})
  in
  List.map idswap_to_aswap p

let rec pterm_to_term env = function
  | PT_App (e1, e2)            -> T_App (pterm_to_term env e1, pterm_to_term env e2)
  | PT_Lam (a, e)              -> T_Lam (pure (A a), pterm_to_term ((a, PI_Atom) :: env) e)
  | PT_Identifier {perm; symb} -> (
    match List.assoc_opt symb env with
    | Some PI_Atom -> T_Atom {perm= idperm_to_aperm perm; symb= A symb}
    | Some PI_Var  -> T_Var {perm= idperm_to_aperm perm; symb= V symb}
    | Some PI_FVar -> raise $ wrong_use "Logical variable" symb "in term context"
    | None         -> raise $ unbound_variable symb )

let pconstr_to_constr env =
  let check_atom a =
    match List.assoc_opt a env with
    | Some PI_Atom -> A a
    | Some PI_Var  -> raise $ wrong_use "Term variable" a "like an atom"
    | Some PI_FVar -> raise $ wrong_use "Logical variable" a "like an atom"
    | None         -> raise $ unbound_variable a
  in
  function
  | PC_Fresh (a, e) -> C_Fresh (check_atom a, pterm_to_term env e)
  | PC_Eq (e1, e2) -> C_Eq (pterm_to_term env e1, pterm_to_term env e2)
  | PC_Shape (e1, e2) -> C_Shape (pterm_to_term env e1, pterm_to_term env e2)
  | PC_Subshape (e1, e2) -> C_Subshape (pterm_to_term env e1, pterm_to_term env e2)
  | PC_AtomNeq ({perm= p1; symb= a1}, {perm= p2; symb= a2}) ->
      C_AtomNeq
        ( check_atom a1
        , permute $ reverse (idperm_to_aperm p1) $ {perm= idperm_to_aperm p2; symb= check_atom a2}
        )

let rec pkind_to_kind env = function
  | PK_Prop              -> K_Prop
  | PK_Arrow (k1, k2)    -> K_Arrow (pkind_to_kind env k1, pkind_to_kind env k2)
  | PK_Constr (c, k)     -> K_Constr (pconstr_to_constr env c, pkind_to_kind env k)
  | PK_ForallAtom (a, k) -> K_ForallAtom (A a, pkind_to_kind ((a, PI_Atom) :: env) k)
  | PK_ForallTerm (x, k) -> K_ForallTerm (V x, pkind_to_kind ((x, PI_Var) :: env) k)

let rec pformula_to_formula env = function
  | PF_Top                 -> F_Top
  | PF_Bot                 -> F_Bot
  | PF_Constr c            -> F_Constr (pconstr_to_constr env c)
  | PF_Or fs               -> F_Or (List.map (pformula_to_formula env) fs)
  | PF_And fs              -> F_And (List.map (pformula_to_formula env) fs)
  | PF_Impl (f1, f2)       -> F_Impl (pformula_to_formula env f1, pformula_to_formula env f2)
  | PF_ForallTerm (v, f)   -> F_ForallTerm (V v, pformula_to_formula ((v, PI_Var) :: env) f)
  | PF_ForallAtom (a, f)   -> F_ForallAtom (A a, pformula_to_formula ((a, PI_Atom) :: env) f)
  | PF_ExistsTerm (v, f)   -> F_ExistsTerm (V v, pformula_to_formula ((v, PI_Var) :: env) f)
  | PF_ExistsAtom (a, f)   -> F_ExistsAtom (A a, pformula_to_formula ((a, PI_Atom) :: env) f)
  | PF_ConstrAnd (c, f)    -> F_ConstrAnd (pconstr_to_constr env c, pformula_to_formula env f)
  | PF_ConstrImpl (c, f)   -> F_ConstrImpl (pconstr_to_constr env c, pformula_to_formula env f)
  | PF_Var x               -> (
    match List.assoc_opt x env with
    | Some PI_Atom -> raise $ wrong_use "Atom" x "as a logical variable"
    | Some PI_Var  -> raise $ wrong_use "Term variable" x "as a logical variable"
    | Some PI_FVar -> F_Var (FV x)
    | None         -> raise $ unbound_variable x )
  | PF_Fun (x, k, f)       ->
      let env = (x, PI_FVar) :: env in
      F_Fun (FV x, pkind_to_kind env k, pformula_to_formula env f)
  | PF_FunAtom (a, f)      -> F_FunAtom (A a, pformula_to_formula ((a, PI_Atom) :: env) f)
  | PF_FunTerm (x, f)      -> F_FunTerm (V x, pformula_to_formula ((x, PI_Atom) :: env) f)
  | PF_AppIdentfier (f, x) -> (
    match List.assoc_opt x env with
    | Some PI_Atom -> F_AppAtom (pformula_to_formula env f, A x)
    | Some PI_Var  -> F_AppTerm (pformula_to_formula env f, var (V x))
    | Some PI_FVar -> F_App (pformula_to_formula env f, F_Var (FV x))
    | None         -> raise $ unbound_variable x )
  | PF_App (f1, f2)        -> F_App (pformula_to_formula env f1, pformula_to_formula env f2)
  | PF_AppTerm (f, t)      -> F_AppTerm (pformula_to_formula env f, pterm_to_term env t)
  | PF_Fix (x, fix, k, f)  ->
      let env = (x, PI_FVar) :: (fix, PI_Var) :: env in
      F_Fix (FV x, V fix, pkind_to_kind env k, pformula_to_formula env f)

let parse_term s = pterm_to_term [] $ parse term s

let parse_constr s = pconstr_to_constr [] $ parse constr s

let parse_kind s = pkind_to_kind [] $ parse kind s

let parse_formula s = pformula_to_formula [] $ parse formula s