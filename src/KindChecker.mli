open Types

(** [kind_check env k f] returns [[]; env |- f : k] *)
val kind_check : KindCheckerEnv.t -> kind -> formula -> bool


(** [subkind env k1 k2] returns [[]; env |- k1 <= k2] *)
val subkind : KindCheckerEnv.t -> kind -> kind -> bool
