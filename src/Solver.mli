open Types
open SolverEnv

module Solver : sig
  val solve : constr -> bool

  val solve_with_env : SolverEnv.t -> constr -> bool
end
