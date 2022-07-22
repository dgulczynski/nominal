open Nominal.Parser
open Nominal.ParserCommon
open Nominal.Permutation
open Nominal.Types
open Nominal.Common
open Nominal.Printing

let string_of_penv env =
  let string_of_pidkind = function
    | PI_Atom -> "atom"
    | PI_Var  -> "var"
    | PI_FVar -> "l.var"
  in
  let string_of_pid (x, k) = Printf.sprintf "%s : %s" x (string_of_pidkind k) in
  string_of_list string_of_pid env

let test name parser convert string_of env source result =
  let actual =
    try convert env (parse parser source)
    with ParserException e ->
      Printf.printf "❌ Error parsing \"%s\": %s\n" source e ;
      assert false
  in
  let pass = actual = result in
  Printf.printf "%s Parsing %s \"%s\" into `%s` %s %s\n"
    (if pass then "✅" else "❌")
    name source (string_of result)
    ( match env with
    | []  -> ""
    | env -> Printf.sprintf "with %s" $ string_of_penv env )
    (if pass then "" else Printf.sprintf "incorrect: %s" $ string_of actual) ;
  assert pass

let test_term = test "term" term pterm_to_term string_of_term

let test_constr = test "constr" constr pconstr_to_constr string_of_constr

let test_kind = test "kind" kind pkind_to_kind string_of_kind

let test_formula = test "formula" formula pformula_to_formula string_of_formula

let _ = test_term [("a", PI_Atom)] "a" $ atom (A "a")

let _ =
  test_term [("a", PI_Atom)] "[a a] [a a] a"
  $ T_Atom {perm= [(pure (A "a"), pure (A "a")); (pure (A "a"), pure (A "a"))]; symb= A "a"}

let _ = test_term [] "a.a" $ T_Lam (pure (A "a"), atom (A "a"))

let _ =
  test_term [] "(a.a) (a.a)"
  $ T_App (T_Lam (pure (A "a"), atom (A "a")), T_Lam (pure (A "a"), atom (A "a")))

let _ =
  test_term [("a", PI_Var)] "a a (a.a) a a"
  $ T_App
      ( T_App
          (T_App (T_App (var (V "a"), var (V "a")), T_Lam (pure (A "a"), atom (A "a"))), var (V "a"))
      , var (V "a") )

let _ =
  test_term [("x", PI_Var)] "(a.a a) x (a.a) x"
  $ T_App
      ( T_App
          ( T_App (T_Lam (pure (A "a"), T_App (atom (A "a"), atom (A "a"))), var (V "x"))
          , T_Lam (pure (A "a"), atom (A "a")) )
      , var (V "x") )

let _ = test_constr [("a", PI_Atom)] "a = a" $ C_Eq (atom (A "a"), atom (A "a"))

let _ = test_constr [("x", PI_Var)] "x = x" $ C_Eq (var (V "x"), var (V "x"))

let _ =
  test_constr [("a", PI_Atom); ("x", PI_Var)] "a # (a. (x a))"
  $ C_Fresh (A "a", T_Lam (pure (A "a"), T_App (var (V "x"), atom (A "a"))))

let _ =
  test_constr [("a", PI_Atom); ("x", PI_Var)] "(a.a) (a.a) ~ a x (a.a)"
  $ C_Shape
      ( T_App (T_Lam (pure (A "a"), atom (A "a")), T_Lam (pure (A "a"), atom (A "a")))
      , T_App (T_App (atom (A "a"), var (V "x")), T_Lam (pure (A "a"), atom (A "a"))) )

let _ =
  test_constr [("a", PI_Atom); ("x", PI_Var)] "(a.a) < a (a.a)"
  $ C_Subshape
      (T_Lam (pure (A "a"), atom (A "a")), T_App (atom (A "a"), T_Lam (pure (A "a"), atom (A "a"))))

let _ =
  test_constr [("a", PI_Atom); ("b", PI_Atom); ("c", PI_Atom); ("d", PI_Atom)] "[a b]a =/= [c d] c"
  $ C_AtomNeq
      (A "a", {perm= [(pure (A "a"), pure (A "b")); (pure (A "c"), pure (A "d"))]; symb= A "c"})

let _ = test_kind [] "*" K_Prop

let _ = test_kind [] "prop => prop" $ K_Arrow (K_Prop, K_Prop)

let _ =
  test_kind [("a", PI_Atom); ("b", PI_Atom); ("x", PI_Var)] "([a # x] prop) => [b # [a b] x] prop"
  $ K_Arrow
      ( K_Constr (C_Fresh (A "a", var $ V "x"), K_Prop)
      , K_Constr (C_Fresh (A "b", T_Var {perm= [(pure (A "a"), pure (A "b"))]; symb= V "x"}), K_Prop)
      )

let _ =
  test_kind [] "forall a : atom. forall x : term. [a # x] (prop => prop)"
  $ K_ForallAtom
      ( A "a"
      , K_ForallTerm (V "x", K_Constr (C_Fresh (A "a", var $ V "x"), K_Arrow (K_Prop, K_Prop))) )

let _ =
  test_formula [] "FORALL a : ATOM. ForAll x : Term. [a # x] => TRUE"
  $ F_ForallAtom (A "a", F_ForallTerm (V "x", F_ConstrImpl (C_Fresh (A "a", var $ V "x"), F_Top)))

let _ =
  test_formula [] "fun f : prop -> forall a : atom. forall x : term. [a # x] => f a {x} {[a a] x}"
  $ F_Fun
      ( FV "f"
      , K_Prop
      , F_ForallAtom
          ( A "a"
          , F_ForallTerm
              ( V "x"
              , F_ConstrImpl
                  ( C_Fresh (A "a", var $ V "x")
                  , F_AppTerm
                      ( F_AppTerm (F_AppAtom (F_Var (FV "f"), A "a"), var (V "x"))
                      , T_Var {perm= [(pure (A "a"), pure (A "a"))]; symb= V "x"} ) ) ) ) )
