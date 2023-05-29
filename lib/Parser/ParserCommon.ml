open Common
open Permutation
open Angstrom

exception ParserException of string

let is_whitespace = function
  | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
  | _ -> false

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false

let is_letter = function
  | 'a' .. 'z' | 'A' .. 'Z' -> true
  | _ -> false

let is_underscore = function
  | '_' -> true
  | _ -> false

let is_apostrophe = function
  | '\'' -> true
  | _ -> false

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
    (take1 (any [is_digit; is_letter; is_underscore]))
    (take_while (any [is_digit; is_letter; is_underscore; is_apostrophe]))

let parenthesized ?(left = '(') ?(right = ')') f = char left *> whitespace *> f <* whitespace <* char right

let parens_op f = parenthesized f <|> f

let binop left op right =
  let* l = left in
  let* _ = whitespace *> string op <* whitespace in
  let* r = right in
  return (l, r)

let bracketed p = parenthesized ~left:'[' ~right:']' p

let brackets_op f = bracketed f <|> f

let braced p = parenthesized ~left:'{' ~right:'}' p

let arrow = string "->" <|> string "→"

let double_arrow = string "=>" <|> string "⇒"

let wedge = string {|/\|} <|> string "∧"

let vee = string {|\/|} <|> string "∨"

let sep_by2 s p = p <* s >>= fun head -> sep_by1 s p >>| fun tail -> head :: tail

let swap =
  bracketed
  $ let* a1 = identifier in
    let* _ = whitespace in
    let* a2 = identifier in
    return (pure a1, pure a2)

let permuted p =
  let* perm = many (swap <* whitespace) in
  let* symb = p in
  return {symb; perm}

let annoted t = whitespace *> string ":" *> whitespace *> t

let optional p = option None (p >>| some)

let typed p typ =
  parens_op
  $ let* x = p in
    let* t = annoted typ in
    return $ (x, t)

let typed_op p typ =
  parens_op
  $ let* x = p in
    let* t = optional $ annoted typ in
    return $ (x, t)

let quantifier q x = q *> whitespace1 *> x <* whitespace <* char '.' <* whitespace

let forall x = quantifier (string_ci "forall" <|> string "∀") x

let exists x = quantifier (string_ci "exists" <|> string "∃") x

let quantifier_without_kind_annotation q x =
  ParserException
    (Printf.sprintf "%s %s quantifier must be used with '%s : atom' or '%s : term' kind annotation" q x x x)

let list_of ?(sep = ";") ?(left = "") ?(right = "") elem =
  string left *> sep_by (whitespace *> string sep <* whitespace) elem <* string right

let list_of' elem = list_of ~sep:"" elem

let on_parsing_error source error =
  let exn = Printf.sprintf "Failed to parse '%s' with error %s" source error in
  raise $ ParserException exn

let run_with_catch on_error f x = try f x with ParserException e -> on_error e

let parse p s =
  let ok = id and error e = raise $ ParserException e in
  Result.fold ~ok ~error $ parse_string ~consume:Consume.All p s
