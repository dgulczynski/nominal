open Nominal.Parser
open Nominal.ParserCommon
open Nominal.Permutation
open Nominal.ProofEquiv
open Nominal.Types
open Nominal.Common
open Nominal.Printing
open Nominal.Utils

let test name parser convert string_of ( === ) env source expected =
  let actual =
    try convert env (parse parser source)
    with ParserException e ->
      Printf.printf "❌ Error parsing \"%s\": %s\n" source e ;
      assert false
  in
  let pass = actual === expected in
  Printf.printf "%s Parsed %s \"%s\" into `%s` %s%s\n"
    (if pass then "✅" else "❌")
    name source (string_of actual)
    ( match env with
    | [] -> ""
    | env -> Printf.sprintf "with %s " $ string_of_bound_env env )
    (if pass then "" else Printf.sprintf "instead of `%s`" $ string_of expected) ;
  assert pass

let test_term = test "term" term pterm_to_term string_of_term ( = )

let test_constr = test "constr" constr pconstr_to_constr string_of_constr ( = )

let test_kind = test "kind" kind pkind_to_kind string_of_kind ( = )

let test_formula env =
  test "formula" formula pformula_to_formula (string_of_formula_in_env env)
    (fun f g -> Nominal.ProofEnv.env env [] [] [] id |> (f === g))
    env

let _ =
  let a_ = 0 in
  let a = A a_ in
  test_term [Bind ("a", K_Atom a_)] "a" $ atom a

let _ =
  let a_ = 0 in
  let a = A a_ in
  test_term [Bind ("a", K_Atom a_)] "[a a] [a a] a" $ T_Atom {perm= [(pure a, pure a); (pure a, pure a)]; symb= a}

let _ =
  let a_ = 0 in
  let a = A a_ in
  test_term [Bind ("a", K_Atom a_)] "a.a" $ T_Lam (pure a, atom a)

let _ =
  let a_ = 0 in
  let a = A a_ in
  test_term [Bind ("a", K_Atom a_)] "(a.a) (a.a)" $ T_App (T_Lam (pure a, atom a), T_Lam (pure a, atom a))

let _ =
  let a_ = 0 and x_ = 1 in
  let a = A a_ in
  let x = V x_ in
  test_term [Bind ("a", K_Atom a_); Bind ("x", K_Var x_)] "(a.a a) x (a.a) x"
  $ T_App (T_App (T_App (T_Lam (pure a, T_App (atom a, atom a)), var x), T_Lam (pure a, atom a)), var x)

let _ = print_newline ()

let _ =
  let a_ = 0 in
  let a = A a_ in
  test_constr [Bind ("a", K_Atom a_)] "a = a" $ C_Eq (atom a, atom a)

let _ =
  let x_ = 0 in
  let x = V x_ in
  test_constr [Bind ("x", K_Var x_)] "x = x" $ C_Eq (var x, var x)

let _ =
  let a_ = 0 and x_ = 1 in
  let a = A a_ in
  let x = V x_ in
  test_constr [Bind ("a", K_Atom a_); Bind ("x", K_Var x_)] "a # (a. (x a))"
  $ C_Fresh (a, T_Lam (pure a, T_App (var x, atom a)))

let _ =
  let a_ = 0 and x_ = 1 in
  let a = A a_ in
  let x = V x_ in
  test_constr [Bind ("a", K_Atom a_); Bind ("x", K_Var x_)] "(a.a) (a.a) ~ a x (a.a)"
  $ C_Shape
      (T_App (T_Lam (pure a, atom a), T_Lam (pure a, atom a)), T_App (T_App (atom a, var x), T_Lam (pure a, atom a)))

let _ =
  let a_ = 0 in
  let a = A a_ in
  test_constr [Bind ("a", K_Atom a_)] "(a.a) < a (a.a)"
  $ C_Subshape (T_Lam (pure a, atom a), T_App (atom a, T_Lam (pure a, atom a)))

let _ =
  let a_ = 0 and b_ = 1 and c_ = 2 and d_ = 3 in
  let a = A a_ and b = A b_ and c = A c_ and d = A d_ in
  test_constr
    [Bind ("a", K_Atom a_); Bind ("b", K_Atom b_); Bind ("c", K_Atom c_); Bind ("d", K_Atom d_)]
    "[a b]a =/= [c d] c"
  $ C_AtomNeq (a, {perm= [(pure a, pure b); (pure c, pure d)]; symb= c})

let _ = print_newline ()

let _ = test_kind [] "*" K_Prop

let _ = test_kind [] "prop -> prop" $ K_Arrow (K_Prop, K_Prop)

let _ =
  let a_ = 0 and b_ = 1 and x_ = 2 in
  let a = A a_ and b = A b_ in
  let x = V x_ in
  test_kind [Bind ("a", K_Atom a_); Bind ("b", K_Atom b_); Bind ("x", K_Var x_)] "([a # x] prop) -> [b # [a b] x] prop"
  $ K_Arrow
      (K_Constr (C_Fresh (a, var x), K_Prop), K_Constr (C_Fresh (b, T_Var {perm= [(pure a, pure b)]; symb= x}), K_Prop))

let _ =
  let a = A (fresh () + 2) and x = V (fresh () + 2) in
  test_kind [] "forall a : atom. forall x : term. [a # x] (prop -> prop)"
  $ K_ForallAtom
      (A_Bind ("a", a), K_ForallTerm (V_Bind ("x", x), K_Constr (C_Fresh (a, var x), K_Arrow (K_Prop, K_Prop))))

let _ = print_newline ()

let _ =
  let a = A (fresh () + 2) and x = V (fresh () + 2) in
  test_formula [] "FORALL a : ATOM. ForAll x : Term. [a # x] => TRUE"
  $ F_ForallAtom (A_Bind ("a", a), F_ForallTerm (V_Bind ("x", x), F_ConstrImpl (C_Fresh (a, var x), F_Top)))

let _ =
  let p_ = 0 and q_ = 1 in
  let p = fvar p_ and q = fvar q_ in
  let env = [Bind ("p", K_FVar (p_, K_Prop)); Bind ("q", K_FVar (q_, K_Prop))] in
  test_formula env "(p => q) => (p => (q))" $ F_Impl (F_Impl (p, q), F_Impl (p, q))

let _ =
  let f_ = fresh () + 3 and a_ = fresh () + 3 and x_ = fresh () + 3 in
  let f = fvar f_ in
  let a = A a_ in
  let x = V x_ in
  test_formula [] "fun f : prop -> forall a : atom. forall x : term. [a # x] => f a x {[a a] x}"
  $ F_Fun
      ( FV_Bind ("f", f_, K_Prop)
      , F_ForallAtom
          ( A_Bind ("a", a)
          , F_ForallTerm
              ( V_Bind ("x", x)
              , F_ConstrImpl
                  ( C_Fresh (a, var $ x)
                  , F_AppTerm (F_AppTerm (F_AppAtom (f, pure a), var x), T_Var {perm= [(pure a, pure a)]; symb= x}) ) )
          ) )

let _ = print_newline ()

let _ =
  let t_ = fresh () + 4 and fix_ = fresh () + 4 and _ = fresh () + 4 and t'_ = fresh () + 4 in
  let t = V t_ and t' = V t'_ in
  test_formula [] "fix ExistsSmaller(t) : Prop = exists t':term. t' < t"
  $ F_Fix
      ( FV_Bind ("ExistsSmaller", fix_, fix_kind t t' "t'" K_Prop)
      , V_Bind ("t", t)
      , K_Prop
      , F_ExistsTerm (V_Bind ("t'", t'), F_Constr (var t' <: var t)) )

let _ = print_newline ()
