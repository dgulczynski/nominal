open Easy_format
open Types
open Utils

type printer = bound_env -> Easy_format.t

(** global margin for pretty-printing*)
let margin = 120

let str x _ = Atom (x, Easy_format.atom)

let with_prefix_suffix prefix suffix x env =
  let prefix_suffix_list_style =
    { list with
      space_after_opening= false
    ; space_after_separator= false
    ; space_before_separator= false
    ; separators_stick_left= false
    ; space_before_closing= false
    ; align_closing= false
    ; stick_to_label= false
    ; wrap_body= `Never_wrap
    ; indent_body= 0 }
  in
  List ((prefix, "", suffix, prefix_suffix_list_style), [x env])

let with_prefix prefix = with_prefix_suffix prefix ""

let with_suffix suffix = with_prefix_suffix "" suffix

let parenthesis_like opening closing x env =
  let parenthesis_list_style =
    { list with
      space_after_opening= false
    ; space_after_separator= false
    ; space_before_separator= false
    ; separators_stick_left= false
    ; space_before_closing= false
    ; align_closing= true
    ; stick_to_label= true
    ; wrap_body= `No_breaks
    ; indent_body= 0 }
  in
  List ((opening, "", closing, parenthesis_list_style), [x env])

let parenthesized = parenthesis_like "(" ")"

let bracketed = parenthesis_like "[" "]"

let braced = parenthesis_like "{" "}"

let backticked = with_prefix_suffix "`" "`"

let pretty_list' style ~left ~sep ~right xs env = List ((left, sep, right, style), List.map (( |> ) env) xs)

let list_without_border_spaces_style =
  { list with
    space_after_opening= false
  ; space_before_closing= false
  ; align_closing= false
  ; stick_to_label= false
  ; separators_stick_left= false }

let pretty_list = pretty_list' list_without_border_spaces_style

let sequence = pretty_list ~left:"" ~sep:"" ~right:""

let concat =
  let concat_style = {list_without_border_spaces_style with space_after_separator= false; wrap_body= `No_breaks} in
  pretty_list' concat_style ~left:"" ~sep:"" ~right:""

let unwords =
  let unwords_style = {list_without_border_spaces_style with wrap_body= `No_breaks} in
  pretty_list' unwords_style ~left:"" ~sep:"" ~right:""

let unlines =
  let unlines_style =
    { list_without_border_spaces_style with
      wrap_body= `Force_breaks
    ; space_before_separator= false
    ; space_after_separator= false }
  in
  pretty_list' unlines_style ~left:"" ~sep:"" ~right:""

let pretty_ocaml_list =
  let ocaml_style =
    { list with
      wrap_body= `Never_wrap
    ; align_closing= true
    ; stick_to_label= true
    ; space_after_opening= true
    ; space_before_closing= true
    ; space_before_separator= true
    ; separators_stick_left= true }
  in
  pretty_list' ocaml_style ~left:"[" ~sep:";" ~right:"]"

let pretty_ocaml_vlist =
  let ocaml_vstyle =
    { list with
      wrap_body= `Force_breaks_rec
    ; align_closing= true
    ; stick_to_label= true
    ; space_after_opening= true
    ; space_before_closing= true
    ; space_before_separator= true
    ; separators_stick_left= true }
  in
  pretty_list' ocaml_vstyle ~left:"[" ~sep:";" ~right:"]"

let pretty_label label body env =
  let label_style = {Easy_format.label with indent_after_label= 2; label_break= `Never} in
  Label ((label env, label_style), body env)

let pretty_unop op x = pretty_label (str op) x

let pretty_multi_op op =
  let multi_op_style =
    { list with
      space_after_opening= false
    ; space_before_closing= false
    ; space_after_separator= true
    ; space_before_separator= true
    ; align_closing= false
    ; stick_to_label= true
    ; separators_stick_left= false
    ; wrap_body= `Never_wrap }
  in
  pretty_list' multi_op_style ~left:"" ~sep:op ~right:""

let pretty_binop x op y = pretty_multi_op op [x; y]

let pretty_binop_unbreaking x op y = unwords [x; str op; y]

let with_binders binds x env =
  let rec find_free env name i =
    let name = Printf.sprintf "%s'%d" name i in
    match bind_by_name name env with
    | None -> name
    | Some _ -> find_free env name (succ i)
  in
  let add_bind env (Bind (name, rep) as bind) =
    match bind_by_name name env with
    | None -> bind :: env
    | Some (Bind (_, rep')) when rep = rep' -> env
    | Some _ -> Bind (find_free env name 1, rep) :: env
  in
  let env = List.fold_left add_bind env binds in
  x env

let pretty_identifier ~on_not_found x env =
  match bind_by_rep x env with
  | Some (Bind (name, _)) -> str name env
  | None -> on_not_found x env

let printer_to_string printer env x = printer x env |> Pretty.to_string

let printer_to_pp_printer printer env fmt x =
  Format.pp_set_margin fmt margin ;
  printer x env |> Pretty.to_formatter fmt

let print printer env =
  let fmt = Format.formatter_of_out_channel stdout in
  printer_to_pp_printer printer env fmt

let print_endline printer env x = print printer env x |> print_newline
