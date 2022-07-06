open Angstrom

let is_whitespace = function
  | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
  | _                                 -> false

let is_digit = function
  | '0' .. '9' -> true
  | _          -> false

let is_letter = function
  | 'a' .. 'z' | 'A' .. 'Z' -> true
  | _                       -> false

let is_underscore = function
  | '_' -> true
  | _   -> false

let whitespace = take_while is_whitespace

let whitespace1 = take_while1 is_whitespace

let take1 f = satisfy f >>| String.make 1

let concat f1 f2 =
  let* first = f1 in
  let* second = f2 in
  return (first ^ second)

let any fs x = List.exists (fun f -> f x) fs

let identifier =
  concat
    (take1 (any [is_letter; is_underscore]))
    (take_while (any [is_digit; is_letter; is_underscore]))

let atom = identifier >>| fun a -> Types.A a

let parenthesized ?(left = '(') ?(right = ')') f =
  char left *> whitespace *> f <* whitespace <* char right

let parens_op f = parenthesized f <|> f

let binop left op right =
  let* l = left in
  let* _ = whitespace *> string op <* whitespace in
  let* r = right in
  return (l, r)

let bracketed p = parenthesized ~left:'[' ~right:']' p

let braced p = parenthesized ~left:'{' ~right:'}' p

let arrow = string "->" <|> string "→"

let double_arrow = string "=>" <|> string "⇒"

let wedge = string {|/\|} <|> string "∧"

let vee = string {|\/|} <|> string "∨"

let sep_by2 s p = p <* s >>= fun head -> sep_by1 s p >>| fun tail -> head :: tail

let quantifier quantifier var =
  quantifier *> whitespace1 *> var <* whitespace <* char '.' <* whitespace

let forall var = quantifier (string "forall" <|> string "∀") var

let exists var = quantifier (string "exists" <|> string "∃") var

let parse p s =
  match parse_string ~consume:Consume.All p s with
  | Ok v    -> v
  | Error e -> failwith e
