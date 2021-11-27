open Types

val free_vars_of : term -> var list

val subst : var -> term -> term -> term
