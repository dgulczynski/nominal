let ( $ ) f x = f x

let ( <| ) f x = f x

let ( % ) f g x = f (g x)

let ( %% ) f g x = f % g x

let ( <$> ) = Option.map

let ( >>= ) = Option.bind

let some = Option.some

let none = Option.none

let flip f x y = f y x

let ( %> ) f g = g % f

let id x = x

let curry f x y = f (x, y)

let uncurry f (x, y) = f x y

let hd_opt = function
  | [] -> None
  | x :: _ -> Some x

let null = function
  | [] -> true
  | _ :: _ -> false

let const x _ = x

let const2 x _ _ = x

let pair x y = (x, y)

let on_fst f (x, y) = (f x, y)

let on_snd f (x, y) = (x, f y)

let pair_eq ( = ) (x1, x2) (y1, y2) = (x1 = y1 && x2 = y2) || (x1 = y2 && x2 = y1)

let to_option a test = if test then Some a else None

let rec find_first test = function
  | [] -> (None, [])
  | x :: xs when test x -> (Some x, xs)
  | x :: xs ->
    let found, rest = find_first test xs in
    (found, x :: rest)

let rec forall2 test xs ys =
  match (xs, ys) with
  | x :: xs, y :: ys -> test x y && forall2 test xs ys
  | xs, ys -> null xs && null ys

let yank x = List.partition (( = ) x)

let unwords = String.concat " "

let unlines = String.concat "\n"
