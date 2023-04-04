open Nominal.Parser
open Nominal.ParserCommon
open Nominal.Permutation
open Nominal.Types
open Nominal.Common
open Nominal.Printing
open Nominal.Utils

let test name parser convert string_of env source result =
  let actual =
    try convert env (parse parser source)
    with ParserException e ->
      Printf.printf "❌ Error parsing \"%s\": %s\n" source e ;
      assert false
  in
  let pass = actual = result in
  Printf.printf "%s Parsed %s \"%s\" into `%s` %s%s\n"
    (if pass then "✅" else "❌")
    name source (string_of actual)
    ( match env with
    | []  -> ""
    | env -> Printf.sprintf "with %s " $ string_of_identifier_env env )
    (if pass then "" else Printf.sprintf "instead of `%s`" $ string_of result) ;
  assert pass

let test_term = test "term" term pterm_to_term string_of_term

let test_constr = test "constr" constr pconstr_to_constr string_of_constr

let test_kind = test "kind" kind pkind_to_kind string_of_kind

let test_formula env = test "formula" formula pformula_to_formula (string_of_formula_in_env env) env

let _ = test_term (atoms_env ["a"]) "a" $ atom (A "a")

let _ =
  test_term (atoms_env ["a"]) "[a a] [a a] a"
  $ T_Atom {perm= [(pure (A "a"), pure (A "a")); (pure (A "a"), pure (A "a"))]; symb= A "a"}

let _ = test_term [] "a.a" $ T_Lam (pure (A "a"), atom (A "a"))

let _ =
  test_term [] "(a.a) (a.a)"
  $ T_App (T_Lam (pure (A "a"), atom (A "a")), T_Lam (pure (A "a"), atom (A "a")))

let _ =
  test_term (vars_env ["a"]) "a a (a.a) a a"
  $ T_App
      ( T_App
          (T_App (T_App (var (V "a"), var (V "a")), T_Lam (pure (A "a"), atom (A "a"))), var (V "a"))
      , var (V "a") )

let _ =
  test_term (vars_env ["x"]) "(a.a a) x (a.a) x"
  $ T_App
      ( T_App
          ( T_App (T_Lam (pure (A "a"), T_App (atom (A "a"), atom (A "a"))), var (V "x"))
          , T_Lam (pure (A "a"), atom (A "a")) )
      , var (V "x") )

let _ = print_newline ()

let _ = test_constr (atoms_env ["a"]) "a = a" $ C_Eq (atom (A "a"), atom (A "a"))

let _ = test_constr (vars_env ["x"]) "x = x" $ C_Eq (var (V "x"), var (V "x"))

let _ =
  test_constr (atoms_env ["a"] @ vars_env ["x"]) "a # (a. (x a))"
  $ C_Fresh (A "a", T_Lam (pure (A "a"), T_App (var (V "x"), atom (A "a"))))

let _ =
  test_constr (atoms_env ["a"] @ vars_env ["x"]) "(a.a) (a.a) ~ a x (a.a)"
  $ C_Shape
      ( T_App (T_Lam (pure (A "a"), atom (A "a")), T_Lam (pure (A "a"), atom (A "a")))
      , T_App (T_App (atom (A "a"), var (V "x")), T_Lam (pure (A "a"), atom (A "a"))) )

let _ =
  test_constr (atoms_env ["a"] @ vars_env ["x"]) "(a.a) < a (a.a)"
  $ C_Subshape
      (T_Lam (pure (A "a"), atom (A "a")), T_App (atom (A "a"), T_Lam (pure (A "a"), atom (A "a"))))

let _ =
  test_constr (atoms_env ["a"; "b"; "c"; "d"]) "[a b]a =/= [c d] c"
  $ C_AtomNeq
      (A "a", {perm= [(pure (A "a"), pure (A "b")); (pure (A "c"), pure (A "d"))]; symb= A "c"})

let _ = print_newline ()

let _ = test_kind [] "*" K_Prop

let _ = test_kind [] "prop -> prop" $ K_Arrow (K_Prop, K_Prop)

let _ =
  test_kind (atoms_env ["a"; "b"] @ vars_env ["x"]) "([a # x] prop) -> [b # [a b] x] prop"
  $ K_Arrow
      ( K_Constr (C_Fresh (A "a", var $ V "x"), K_Prop)
      , K_Constr (C_Fresh (A "b", T_Var {perm= [(pure (A "a"), pure (A "b"))]; symb= V "x"}), K_Prop)
      )

let _ =
  test_kind [] "forall a : atom. forall x : term. [a # x] (prop -> prop)"
  $ K_ForallAtom
      ( A "a"
      , K_ForallTerm (V "x", K_Constr (C_Fresh (A "a", var $ V "x"), K_Arrow (K_Prop, K_Prop))) )

let _ = print_newline ()

let _ =
  test_formula [] "FORALL a : ATOM. ForAll x : Term. [a # x] => TRUE"
  $ F_ForallAtom (A "a", F_ForallTerm (V "x", F_ConstrImpl (C_Fresh (A "a", var $ V "x"), F_Top)))

let fvar_representation env x =
  let to_representation = function
    | K_FVar (i, _) -> i
    | _             -> failwith $ x ^ " is not an l.var"
  in
  to_representation (List.assoc x env)

let _ =
  let env = fvars_env [("p", K_Prop); ("q", K_Prop)] in
  let p = fvar $ fvar_representation env "p" in
  let q = fvar $ fvar_representation env "q" in
  test_formula env "(p => q) => (p => (q))" $ F_Impl (F_Impl (p, q), F_Impl (p, q))

let _ =
  let f = fresh_fvar_arg () + 1 in
  (* very hacky: f will be assigned next fresh number, which will be current fresh number + 1 *)
  test_formula [] "fun f : prop -> forall a : atom. forall x : term. [a # x] => f a x {[a a] x}"
  $ F_Fun
      ( FV_Bind ("f", f, K_Prop)
      , F_ForallAtom
          ( A "a"
          , F_ForallTerm
              ( V "x"
              , F_ConstrImpl
                  ( C_Fresh (A "a", var $ V "x")
                  , F_AppTerm
                      ( F_AppTerm (F_AppAtom (fvar f, A "a"), var (V "x"))
                      , T_Var {perm= [(pure (A "a"), pure (A "a"))]; symb= V "x"} ) ) ) ) )

let _ = print_newline ()

let _ =
  let y = V "_v0" in
  (* very hacky: y will be assigned next fresh var, which will should be current _v0 *)
  let fix = fresh_fvar_arg () + 1 in
  (* very hacky: X will be assigned next fresh number, which will be current fresh number + 1 *)
  test_formula [] "fix Type(t) : Prop = exists t':term. t' < t"
  $ F_Fix
      ( FV_Bind ("Type", fix, fix_kind (V "t") y K_Prop)
      , V "t"
      , K_Prop
      , F_ExistsTerm (V "t'", F_Constr (var (V "t'") <: var (V "t"))) )

let _ = print_newline ()
