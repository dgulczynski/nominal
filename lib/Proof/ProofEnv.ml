open Format
open Common

type 'a env = 'a list

let empty = []

let singleton f = [f]

let union e1 e2 = List.merge compare e1 e2

let add item = List.merge compare (singleton item)

let map = List.map

let to_list = id

let from_list = id

let lookup env test = List.find_opt test env

let remove env test = List.filter (not % test) env

let pp_print_env pp_print_assupmtion =
  let pp_sep fmt () = pp_print_string fmt "; " in
  pp_print_list ~pp_sep pp_print_assupmtion
