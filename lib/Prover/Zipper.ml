type 'a zipper = {left: 'a list; right: 'a list} (* right can only be empty if left is empty *)

let from_list xs = {left= []; right= xs}

let to_list {left; right} = List.rev_append left right

let is_empty {right; _} =
  match right with
  | []     -> true
  | _ :: _ -> false

let insert x {left; right} = {left; right= x :: right}

let move_back_if_not_empty {left; right} =
  match left with
  | []      -> {left; right}
  | x :: xs -> {left= xs; right= x :: right}

let move_forward {left; right} =
  match right with
  | []      -> failwith "move_forward on rightmost"
  | x :: xs -> {left= x :: left; right= xs}

let extract_current {left; right} =
  match right with
  | []      -> failwith "extract_current on empty"
  | [x]     -> (x, move_back_if_not_empty {left; right= []})
  | x :: xs -> (x, {left; right= xs})

let rec extract_first test ({right; _} as z) =
  match right with
  | [] -> None
  | x :: _ when test x -> Some (extract_current z)
  | _ -> extract_first test (move_forward z)

let exists test {left; right} = List.exists test left || List.exists test right
