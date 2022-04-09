open Types

val kind_check : KindCheckerEnv.t -> kind -> formula -> bool
(** [kind_check env k f] returns [[]; env |- f : k] *)

val subkind : KindCheckerEnv.t -> kind -> kind -> bool
(** [subkind env k1 k2] returns [[]; env |- k1 <= k2] *)

val ( <=. ) : kind -> kind -> bool
(** [k1 <=. k2] is [subkind empty k1 k2]*)
