open Types

val kind_check : KindCheckerEnv.t -> kind -> formula -> bool

val subkind : KindCheckerEnv.t -> kind -> kind -> bool
