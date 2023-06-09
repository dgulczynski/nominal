open Nominal
open Types
open Prelude
open KindChecker
open Permutation
open PrettyPrinting
open PrettyPrintingCore
open Solver

let print_result env expr res =
  let desc _ =
    unwords
      [ str (if res then "✅" else "❌")
      ; str "Solver"
      ; str (if res then "ran successfully" else "failed solving")
      ; env
      ; str "⊢"
      ; expr ]
  in
  if res then print_endline desc [] () else failwith $ printer_to_string desc [] ()

let print_solver assms c =
  print_result (pretty_ocaml_list $ List.map pretty_constr assms) (pretty_constr c) (assms |-: c)

let print_subkind_solver (k1, k2) =
  print_result (str "[]") (unwords [pretty_kind k1; str "≤"; pretty_kind k2]) $ (k1 <=: k2) KindCheckerEnv.empty

let print_kind_solver (formula, kind) =
  print_result (str "[]") (unwords [pretty_formula formula; str ":"; pretty_kind kind])
  $ (formula -: kind) KindCheckerEnv.empty

let examples =
  let a_ = A 0 and b_ = A 1 and c_ = A 2 in
  let a = {perm= []; symb= a_} and b = {perm= []; symb= b_} and c = {perm= []; symb= c_} in
  let pi = [(b, c)] in
  let x = T_Var {perm= []; symb= V 3} in
  [ x =: x
  ; a_ #: (T_Lam (a, T_Atom a))
  ; a_ #: (permute_term [] (T_Lam (b, T_Atom b)))
  ; a_ #: (permute_term pi (T_Lam (b, T_Atom b)))
  ; T_App (T_Atom a, T_Atom b) =: T_App (T_Atom a, T_Atom b)
  ; T_Lam (a, T_Atom a) =: T_Lam (b, T_Atom b)
  ; T_Lam (a, T_Atom a) =~: T_Lam (b, T_Atom b)
  ; T_Atom a <: T_Lam (b, T_Atom b) ]

let subkind_examples =
  [ (K_Prop, K_Prop)
  ; (K_ForallTerm (V_Bind ("x", fresh_var ()), K_Prop), K_ForallTerm (V_Bind ("y", fresh_var ()), K_Prop)) ]

let kind_examples = [(F_Bot, K_Prop)]

let _ = List.iter (print_solver []) examples

let _ = print_newline ()

let _ =
  let x = var (V 1) and y = var (V 2) and z = var (V 3) and w = var (V 4) and v = var (V 5) and a = pure (A 0) in
  let t = T_Lam (a, T_Atom a) in
  (print_solver [x <: y; y =~: z; z =: t]) (x <: t) ;
  (print_solver [x <: y; y =~: z; z =: t]) (y =~: t) ;
  (print_solver [symbol x; y =~: x]) (symbol y) ;
  (print_solver [symbol x; y <: x]) absurd ;
  (print_solver [z <: x; symbol x; y =~: z]) absurd ;
  (print_solver [z <: x; v =~: w; x =~: y; w =~: z]) (v <: y)

let _ = print_newline ()

let _ = List.iter print_subkind_solver subkind_examples

let _ = print_newline ()

let _ = List.iter print_kind_solver kind_examples

let _ = print_newline ()
