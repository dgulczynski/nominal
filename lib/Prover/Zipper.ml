type 'a zipper = {left: 'a list; right: 'a list} (* right can be empty only if left is empty *)

let from_list xs = {left= []; right= xs}

let to_list {left; right} = List.rev_append left right

let is_empty {right; _} =
  match right with
  | []     -> true
  | _ :: _ -> false

let insert x {left; right} = {left; right= x :: right}

let move_back {left; right} =
  match left with
  | []      -> failwith "move_back on leftmost"
  | x :: xs -> {left= xs; right= x :: right}

let move_forward {left; right} =
  match right with
  | []      -> failwith "move_forward on rightmost"
  | x :: xs -> {left= x :: left; right= xs}

let extract_current {left; right} =
  match right with
  | []      -> failwith "extract_current on empty"
  | x :: xs -> (x, {left; right= xs})

let rec extract_first test ({left; right} as z) =
  match right with
  | [] -> None
  | x :: xs when test x -> Some (x, {left; right= xs})
  | _ -> extract_first test (move_forward z)

let exists test {left; right} = List.exists test left || List.exists test right
