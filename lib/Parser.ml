open Angstrom
open ParserTypes

let term : pterm t = ParserTerm.term

let constr : pconstr t = ParserConstr.constr

let kind : pkind t = ParserKind.kind

let formula : pformula t = ParserFormula.formula

let parse = ParserCommon.parse

let pterm_to_term _ _ = assert false

let pconstr_to_constr _ _ = assert false

let pkind_to_kind _ _ = assert false

let pformula_to_formula _ _ = assert false
