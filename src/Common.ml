open Types

let rec free_vars_of = function
  | Var v        -> [v]
  | Lam (x, e)   -> x :: free_vars_of e
  | App (e1, e2) -> free_vars_of e1 @ free_vars_of e2

let rec subst x e = function
  | Var v when v = x -> e
  | Lam (x', e') when x' != x' -> Lam (x', subst x e e')
  | App (e1, e2) -> App (subst x e e1, subst x e e2)
  | e -> e
