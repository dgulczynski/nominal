open Types

val check : kind -> formula -> bool

val subkind : KindCheckerEnv.t -> kind -> kind -> bool
