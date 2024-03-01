open Types

type printer

val with_prefix_suffix : string -> string -> printer -> printer

val with_prefix : string -> printer -> printer

val with_suffix : string -> printer -> printer

val str : string -> printer

val pretty_list : left:string -> sep:string -> right:string -> printer list -> printer
(** Print a sequence of printers in arbitrary way, with defined opening, closing, and separator  *)

val sequence : printer list -> printer
(** Print a sequence of printers in arbitrary way, only whitespace separated *)

val concat : printer list -> printer
(** Concat printers without separation *)

val unwords : printer list -> printer
(** Concat printers with space, never breaking *)

val unlines : printer list -> printer
(** Concat pritners with newlines, always breaking *)

val pretty_ocaml_list : printer list -> printer
(** Print list like OCaml would *)

val pretty_ocaml_vlist : printer list -> printer
(** Print list like OCaml would, but always vertically *)

val parenthesized : printer -> printer

val bracketed : printer -> printer

val braced : printer -> printer

val backticked : printer -> printer

val pretty_label : printer -> printer -> printer

val pretty_unop : string -> printer -> printer

val pretty_binop : printer -> string -> printer -> printer

val pretty_binop_unbreaking : printer -> string -> printer -> printer
(** Print binop that will not break line *)

val pretty_multi_op : string -> printer list -> printer
(** Print sequence of arguments interspersed with operator *)

val with_binders : binder list -> printer -> printer
(** Add binders to printing env *)

val pretty_identifier : on_not_found:(name_internal -> printer) -> name_internal -> printer
(** Print identifiers name found in env, otherwise [on_not_found] *)

val printer_to_string : ('a -> printer) -> bound_env -> 'a -> string

val print : ('a -> printer) -> bound_env -> 'a -> unit

val print_endline : ('a -> printer) -> bound_env -> 'a -> unit

val printer_to_pp_printer : ('a -> printer) -> bound_env -> Format.formatter -> 'a -> unit
