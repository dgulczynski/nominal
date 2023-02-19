open Angstrom
open Types
open Common
open Permutation
open ParserTypes
open ParserCommon
open Utils

let term : pterm t = ParserTerm.term

let constr : pconstr t = ParserConstr.constr

let kind : pkind t = ParserKind.kind

let formula : pformula t = ParserFormula.formula

let parse = ParserCommon.parse

let unbound_variable x = ParserException (Printf.sprintf "Unbound variable %s" x)

let wrong_use expected x actual = ParserException (Printf.sprintf "%s %s used %s" expected x actual)

let rec idperm_to_aperm p =
  let idswap_to_aswap ({perm= p1; symb= a1}, {perm= p2; symb= a2}) =
    ({perm= idperm_to_aperm p1; symb= A a1}, {perm= idperm_to_aperm p2; symb= A a2})
  in
  List.map idswap_to_aswap p

let rec pterm_to_term env = function
  | PT_App (e1, e2)            -> T_App (pterm_to_term env e1, pterm_to_term env e2)
  | PT_Lam (a, e)              -> T_Lam (pure (A a), pterm_to_term ((a, K_Atom) :: env) e)
  | PT_Identifier {perm; symb} -> (
    match List.assoc_opt symb env with
    | Some K_Atom     -> T_Atom {perm= idperm_to_aperm perm; symb= A symb}
    | Some K_Var      -> T_Var {perm= idperm_to_aperm perm; symb= V symb}
    | Some (K_FVar _) -> raise $ wrong_use "Logical variable" symb "in term context"
    | None            -> raise $ unbound_variable symb )

let pconstr_to_constr env =
  let check_atom a =
    match List.assoc_opt a env with
    | Some K_Atom     -> A a
    | Some K_Var      -> raise $ wrong_use "Term variable" a "like an atom"
    | Some (K_FVar _) -> raise $ wrong_use "Logical variable" a "like an atom"
    | None            -> raise $ unbound_variable a
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
  | PK_ForallAtom (a, k) -> K_ForallAtom (A a, pkind_to_kind ((a, K_Atom) :: env) k)
  | PK_ForallTerm (x, k) -> K_ForallTerm (V x, pkind_to_kind ((x, K_Var) :: env) k)

let rec pformula_to_formula env = function
  | PF_Top                     -> F_Top
  | PF_Bot                     -> F_Bot
  | PF_Constr c                -> F_Constr (pconstr_to_constr env c)
  | PF_Or fs                   -> F_Or (List.map (pformula_to_formula env) fs)
  | PF_And fs                  -> F_And (List.map (pformula_to_formula env) fs)
  | PF_Impl (f1, f2)           -> F_Impl (pformula_to_formula env f1, pformula_to_formula env f2)
  | PF_ForallTerm (v, f)       -> F_ForallTerm (V v, pformula_to_formula ((v, K_Var) :: env) f)
  | PF_ForallAtom (a, f)       -> F_ForallAtom (A a, pformula_to_formula ((a, K_Atom) :: env) f)
  | PF_ExistsTerm (v, f)       -> F_ExistsTerm (V v, pformula_to_formula ((v, K_Var) :: env) f)
  | PF_ExistsAtom (a, f)       -> F_ExistsAtom (A a, pformula_to_formula ((a, K_Atom) :: env) f)
  | PF_ConstrAnd (c, f)        -> F_ConstrAnd (pconstr_to_constr env c, pformula_to_formula env f)
  | PF_ConstrImpl (c, f)       -> F_ConstrImpl (pconstr_to_constr env c, pformula_to_formula env f)
  | PF_Var x                   -> (
    match List.assoc_opt x env with
    | Some K_Atom          -> raise $ wrong_use "Atom" x "as a logical variable"
    | Some K_Var           -> raise $ wrong_use "Term variable" x "as a logical variable"
    | Some (K_FVar (i, _)) -> fvar i
    | None                 -> raise $ unbound_variable x )
  | PF_Fun (x, k, f)           ->
      let i = fresh_fvar_arg () in
      let k = pkind_to_kind env k in
      let env = (x, K_FVar (i, k)) :: env in
      F_Fun (FV_Bind (x, i, k), pformula_to_formula env f)
  | PF_FunAtom (a, f)          -> F_FunAtom (A a, pformula_to_formula ((a, K_Atom) :: env) f)
  | PF_FunTerm (x, f)          -> F_FunTerm (V x, pformula_to_formula ((x, K_Atom) :: env) f)
  | PF_AppIdentfier (f, x)     -> (
    match List.assoc_opt x env with
    | Some K_Atom          -> F_AppAtom (pformula_to_formula env f, A x)
    | Some K_Var           -> F_AppTerm (pformula_to_formula env f, var (V x))
    | Some (K_FVar (i, _)) -> F_App (pformula_to_formula env f, fvar i)
    | None                 -> F_App
                                ( pformula_to_formula env f
                                , pformula_to_formula env $ parse formula x ) )
  | PF_App (f1, f2)            -> F_App (pformula_to_formula env f1, pformula_to_formula env f2)
  | PF_AppTerm (f, t)          -> F_AppTerm (pformula_to_formula env f, pterm_to_term env t)
  | PF_Fix (fix_name, x, k, f) ->
      let y = fresh_var () in
      let env' = (x, K_Var) :: env in
      let k = pkind_to_kind env k in
      let fix_k = fix_kind (V x) y k in
      let fix_i = fresh_fvar_arg () in
      let env'' = (fix_name, K_FVar (fix_i, fix_k)) :: env' in
      F_Fix (FV_Bind (fix_name, fix_i, fix_k), V x, k, pformula_to_formula env'' f)

let parse_atom_in_env env s =
  let raise_not_an_atom_but what =
    let exn = Printf.sprintf "Expected %s to be an atom, not a %s" s what in
    raise $ ParserException exn
  in
  let a = parse identifier s in
  match List.assoc_opt a env with
  | Some K_Atom     -> A a
  | Some K_Var      -> raise_not_an_atom_but "variable"
  | Some (K_FVar _) -> raise_not_an_atom_but "logical variable"
  | None            -> raise $ unbound_variable a

let parse_term_in_env env s = pterm_to_term env $ parse term s

let parse_term = parse_term_in_env []

let parse_constr_in_env env s = pconstr_to_constr env $ parse constr s

let parse_constr = parse_constr_in_env []

let parse_kind s = pkind_to_kind [] $ parse kind s

let parse_formula_in_env env s = pformula_to_formula env $ parse formula s

let parse_formula = parse_formula_in_env []

let judgement assm goal =
  let* env = list_of assm in
  let* _ = whitespace *> string "|-" <* whitespace in
  let* goal in
  return (env, goal)

let run_judgement penv s =
  let env, goal = parse (judgement constr constr) s in
  Solver.solve_with_assumptions
    (List.map (pconstr_to_constr penv) env)
    (pconstr_to_constr penv goal)

let atoms_env xs = List.map (fun a -> (a, K_Atom)) xs

let vars_env xs = List.map (fun x -> (x, K_Var)) xs

let fvars_env xs = List.map (fun (x, k) -> (x, K_FVar (fresh_fvar_arg (), k))) xs
