open Prelude
open Types
open Utils
open KindChecker
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
  {identifiers: bound_env; constraints: constr list; assumptions: 'a list; mapping: mapping; to_formula: 'a -> formula}

let assumptions env = env.assumptions

let identifiers env = env.identifiers

let constraints env = env.constraints

let mapping env = env.mapping

let to_formula env = env.to_formula

let env identifiers constraints assumptions mapping to_formula =
  { assumptions= sort assumptions
  ; constraints= sort constraints
  ; identifiers= sort identifiers
  ; mapping= sort mapping
  ; to_formula }

let empty to_formula = env [] [] [] [] to_formula

let singleton f to_formula = env [] [] [f] [] to_formula

let on_assms f env = {env with assumptions= f env.assumptions}

let on_identifiers f env = {env with identifiers= f env.identifiers}

let on_constraints f env = {env with constraints= f env.constraints}

let on_mapping f env = {env with mapping= f env.mapping}

let set_mapping mapping env = {env with mapping}

let union env =
  on_assms (merge env.assumptions)
  % on_identifiers (merge env.identifiers)
  % on_constraints (merge env.constraints)
  % on_mapping (merge env.mapping)

let name_eq name = function
  | Bind (x, _) -> x = name

let rep_eq name = function
  | Bind (_, K_Atom x) | Bind (_, K_Var x) | Bind (_, K_FVar (x, _)) -> x = name
  | Bind (_, K_Func) -> false

let lookup_identifier name {identifiers; _} = List.find_opt (name_eq name) identifiers

let add_identifier (Bind (x, _) as bind) env =
  match lookup_identifier x env with
  | Some _ -> raise $ name_taken x
  | None -> on_identifiers (merge [bind]) env

let add_fvar x_bind = add_identifier $ fvar_binder_to_binder x_bind

let add_atom a_bind = add_identifier $ atom_binder_to_binder a_bind

let add_var x_bind = add_identifier $ var_binder_to_binder x_bind

let add_constr constr = on_constraints $ merge [constr]

let add_assm ass = on_assms $ merge [ass]

let map_assms f to_formula {assumptions; identifiers; constraints; mapping; _} =
  {assumptions= sort $ List.map f assumptions; identifiers; constraints; mapping; to_formula}

let map_constraints f = on_constraints (List.map f)

let lookup_assm test {assumptions; _} = List.find_opt test assumptions

let unfilter test = List.filter (not % test)

let remove_assms test = on_assms $ unfilter test

let remove_constraints test = on_constraints $ unfilter test

let remove_identifiers test = on_identifiers $ unfilter test

let remove_identifier name = remove_identifiers $ rep_eq name

let all_identifiers env =
  let add_mapping ids {bind= FV_Bind (x_name, x, k); _} = Bind (x_name, K_FVar (x, k)) :: ids in
  List.fold_left add_mapping env.identifiers env.mapping

let kind_checker_env env =
  let add_identifier env = function
    | Bind (x_name, K_FVar (x, k)) -> KindCheckerEnv.map_fvar env x_name (FV x) k
    | _ -> env
  and add_mapping env = function
    | {bind= FV_Bind (x_name, x, k); _} -> KindCheckerEnv.map_fvar env x_name (FV x) k
  in
  let from_identifiers = List.fold_left add_identifier KindCheckerEnv.empty env.identifiers in
  List.fold_left add_mapping from_identifiers env.mapping

let kind_infer env f = KindChecker.kind_infer (kind_checker_env env) f

let bound_in_assm name = List.exists (( = ) name) % free_names_of_formula

let bound_in_constr name = List.exists (( = ) name) % free_names_of_constr

let find_bind name env =
  let from_constr c = F_Constr c in
  let find x =
    match List.find_opt (bound_in_assm x % env.to_formula) env.assumptions with
    | Some f -> Some (env.to_formula f)
    | None -> from_constr <$> List.find_opt (bound_in_constr x) env.constraints
  in
  bind_by_name name env.identifiers >>= binder_rep >>= find

let remove_var name env =
  match List.partition (name_eq name) env.identifiers with
  | Bind (_, K_Var x) :: _, identifiers ->
    {env with identifiers}
    |> on_assms (List.filter (not % bound_in_assm x % env.to_formula))
    |> on_constraints (List.filter (not % bound_in_constr x))
  | _ -> env

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
        | _ -> fresh ()
      in
      {bind= FV_Bind (f_name, f_var, f_kind); body= f_body} :: mapping
    | None -> raise $ cannot_infer_kind f_name
  in
  env identifiers constraints assumptions (List.fold_left aux [] source_mapping) to_formula

let subst_atom subst_assm (A a_rep as a) b env =
  env
  |> on_assms (List.map (subst_assm a b))
  |> on_constraints (List.map (subst_atom_in_constr a b))
  |> on_mapping (List.map (fun {bind; body} -> {bind; body= (a |-> b) body}))
  |> on_identifiers (List.filter (not % rep_eq a_rep))

let subst_var subst_assm (V x_rep as x) t env =
  env
  |> on_assms (List.map (subst_assm x t))
  |> on_constraints (List.map (subst_var_in_constr x t))
  |> on_mapping (List.map (fun {bind; body} -> {bind; body= (x |=> t) body}))
  |> on_identifiers (List.filter (not % rep_eq x_rep))

let solver_env env =
  let constr_assms = List.filter_map (to_constr_op % to_formula env) $ env.assumptions in
  constr_assms @ constraints env

let raise_in_env env exn = raise % exn $ all_identifiers env

let kind_check' env k f =
  match kind_infer env f with
  | Some k' when k' <=: k <| kind_checker_env env -> Result.Ok ()
  | k' -> Result.Error k'

let kind_check env = Result.is_ok %% kind_check' env

let kind_check_throw env k f =
  let ok = id in
  let error = raise_in_env env % formula_kind_mismatch f k in
  Result.fold ~ok ~error $ kind_check' env k f
