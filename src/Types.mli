type atom = A of string

type var = V of string

type term = Var of var | Lam of var * term | App of term * term

type constr = Neq of atom * atom | Fresh of atom * term
