open Types
open KindCheckerEnv

module KindChecker : sig
  val check : kind -> formula -> bool

  val subkind : KindCheckerEnv.t -> kind -> kind -> bool
end
