open Common
open Format
open Printing
open Types
open Utils
open ProofCommon
open ProofException
open Substitution

let sort xs = List.sort_uniq compare xs

let merge xs ys =
  let rec merge xs ys =
    match (xs, ys) with
    | [], zs | zs, [] -> zs
    | x :: xs, y :: ys when x = y -> x :: merge xs ys
    | x :: xs, y :: ys when x < y -> x :: y :: merge xs ys
    | x :: xs, y :: ys -> y :: x :: merge xs ys
  in
  merge (sort xs) (sort ys)

type 'a env =
  { identifiers: bound_env
  ; constraints: constr list
  ; assumptions: 'a list
  ; mapping: mapping
  ; to_formula: 'a -> formula }

let assumptions {assumptions; _} = assumptions

let identifiers {identifiers; _} = identifiers

let constraints {constraints; _} = constraints

let mapping {mapping; _} = mapping

let to_formula {to_formula; _} = to_formula

let env identifiers constraints assumptions mapping to_formula =
  { assumptions= sort assumptions
  ; constraints= sort constraints
  ; identifiers= sort identifiers
  ; mapping= sort mapping
  ; to_formula }

let empty to_formula = env [] [] [] [] to_formula

let singleton f to_formula = env [] [] [f] [] to_formula

let on_assumptions f {assumptions; identifiers; constraints; mapping; to_formula} =
  {assumptions= f assumptions; identifiers; constraints; mapping; to_formula}

let on_identifiers f {assumptions; identifiers; constraints; mapping; to_formula} =
  {assumptions; identifiers= f identifiers; constraints; mapping; to_formula}

let on_constraints f {assumptions; identifiers; constraints; mapping; to_formula} =
  {assumptions; identifiers; constraints= f constraints; mapping; to_formula}

let on_mapping f {assumptions; identifiers; constraints; mapping; to_formula} =
  {assumptions; identifiers; constraints; mapping= f mapping; to_formula}

let set_mapping mapping = on_mapping $ const mapping

let union
    {assumptions= a1; identifiers= i1; constraints= c1; mapping= v1; to_formula}
    {assumptions= a2; identifiers= i2; constraints= c2; mapping= v2; _} =
  { assumptions= merge a1 a2
  ; identifiers= merge i1 i2
  ; constraints= merge c1 c2
  ; mapping= merge v1 v2
  ; to_formula }

let name_eq name = function
  | Bind (x, _) -> x = name

let rep_eq name = function
  | Bind (_, K_Atom x) | Bind (_, K_Var x) | Bind (_, K_FVar (x, _)) -> x = name
  | Bind (_, K_Func) -> false

let lookup_identifier name {identifiers; _} = List.find_opt (name_eq name) identifiers

let add_identifier (Bind (x, _) as bind) env =
  match lookup_identifier x env with
  | Some _ -> raise $ name_taken x
  | None   -> on_identifiers (merge [bind]) env

let add_fvar x_bind = add_identifier $ fvar_binder_to_binder x_bind

let add_atom a_bind = add_identifier $ atom_binder_to_binder a_bind

let add_var x_bind = add_identifier $ var_binder_to_binder x_bind

let add_constr constr = on_constraints $ merge [constr]

let add_assumption ass = on_assumptions $ merge [ass]

let map_assumptions f to_formula {assumptions; identifiers; constraints; mapping; _} =
  {assumptions= sort $ List.map f assumptions; identifiers; constraints; mapping; to_formula}

let map_constraints f = on_constraints (List.map f)

let lookup_assumption test {assumptions; _} = List.find_opt test assumptions

let unfilter test = List.filter (not % test)

let remove_assumptions test = on_assumptions $ unfilter test

let remove_constraints test = on_constraints $ unfilter test

let remove_identifiers test = on_identifiers $ unfilter test

let remove_identifier name = remove_identifiers $ rep_eq name

let all_identifiers {mapping; identifiers; _} =
  let add_mapping ids {bind= FV_Bind (x_name, x, k); _} = Bind (x_name, K_FVar (x, k)) :: ids in
  List.fold_left add_mapping identifiers mapping

let kind_checker_env {identifiers; mapping; _} =
  let add_identifier env = function
    | Bind (x_name, K_FVar (x, k)) -> KindCheckerEnv.map_fvar env x_name (FV x) k
    | _                            -> env
  and add_mapping env = function
    | {bind= FV_Bind (x_name, x, k); _} -> KindCheckerEnv.map_fvar env x_name (FV x) k
  in
  let from_identifiers = List.fold_left add_identifier KindCheckerEnv.empty identifiers in
  List.fold_left add_mapping from_identifiers mapping

let kind_infer env f = KindChecker.kind_infer (kind_checker_env env) f

let bound_in_assumption name = List.exists (( = ) name) % free_names_of_formula

let bound_in_constr name = List.exists (( = ) name) % free_names_of_constr

let find_bind name {assumptions; constraints; to_formula; identifiers; _} =
  let from_constr c = F_Constr c in
  let find x =
    match List.find_opt (bound_in_assumption x % to_formula) assumptions with
    | Some f -> Some (to_formula f)
    | None   -> from_constr <$> List.find_opt (bound_in_constr x) constraints
  in
  bind_by_name name identifiers >>= binder_rep >>= find

let remove_var name ({assumptions; constraints; identifiers; mapping; to_formula} as env) =
  match List.partition (name_eq name) identifiers with
  | Bind (_, K_Var x) :: _, identifiers ->
      { assumptions= List.filter (not % bound_in_assumption x % to_formula) assumptions
      ; constraints= List.filter (not % bound_in_constr x) constraints
      ; identifiers
      ; mapping
      ; to_formula }
  | _                                   -> env

let parse_formula {identifiers; mapping; _} =
  let convert {bind= FV_Bind (x_name, x_var, x_kind); _} = Bind (x_name, K_FVar (x_var, x_kind)) in
  let parse_env = List.fold_left (fun xs x -> convert x :: xs) identifiers mapping in
  Parser.parse_formula_in_env parse_env

let parse_mapping identifiers constraints assumptions to_formula source_mapping =
  let aux mapping (f_name, f_source) =
    let env = env identifiers constraints assumptions mapping to_formula in
    let f_body = parse_formula env f_source in
    match kind_infer env f_body with
    | Some f_kind ->
        let f_var =
          match f_body with
          | F_Fix (FV_Bind (_, x, _), _, _, _) -> x
          | _                                  -> fresh ()
        in
        {bind= FV_Bind (f_name, f_var, f_kind); body= f_body} :: mapping
    | None        -> raise $ cannot_infer_kind f_name
  in
  env identifiers constraints assumptions (List.fold_left aux [] source_mapping) to_formula

let subst_atom subst_assm (A a_rep as a) b {assumptions; identifiers; constraints; mapping; to_formula} =
  let filter_out_a = not % rep_eq a_rep in
  { assumptions= List.map (subst_assm a b) assumptions
  ; identifiers= List.filter filter_out_a identifiers
  ; constraints= List.map (subst_atom_in_constr a b) constraints
  ; mapping= List.map (fun {bind; body} -> {bind; body= (a |-> b) body}) mapping
  ; to_formula }

let subst_var subst_assm (V x_rep as x) t {assumptions; identifiers; constraints; mapping; to_formula} =
  let filter_out_x = not % rep_eq x_rep in
  { assumptions= List.map (subst_assm x t) assumptions
  ; identifiers= List.filter filter_out_x identifiers
  ; constraints= List.map (subst_var_in_constr x t) constraints
  ; mapping= List.map (fun {bind; body} -> {bind; body= (x |=> t) body}) mapping
  ; to_formula }

let solver_env env =
  let constr_assumptions = List.filter_map (to_constr_op % to_formula env) $ assumptions env in
  constr_assumptions @ constraints env

let pp_print_env pp_print_assumption fmt {assumptions; identifiers; constraints; _} =
  let pp_sep fmt () = pp_print_string fmt "\n; " in
  let pp_print_bracketed_list fmt p = function
    | [] -> pp_print_string fmt "[ ]"
    | xs -> pp_print_string fmt "[ " ; pp_print_list ~pp_sep p fmt xs ; pp_print_string fmt "\n]"
  in
  pp_print_newline fmt () ;
  pp_print_bracketed_list fmt (pp_print_constr_in_env identifiers) constraints ;
  pp_print_newline fmt () ;
  pp_print_bracketed_list fmt pp_print_assumption assumptions
