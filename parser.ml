open Batteries

open Angstrom
open Types

(* Helpers *)

let whitespace x = 
  match x with
  | ' ' | '\t' -> true
  | _ -> false

let eat_spaces = take_while whitespace

let parse_tilde = 
  char '~' *> return false
  <|> return true

let ident = take_while1 (function 'a'..'z' | 'A'..'Z' -> true | _ -> false) 

let parens p = char '(' *> p <* char ')'

let comma = char ','

(* Main parsers *)

(* let rec expr() : string term t = *)
let parser_term : string term t =
  fix (fun expr ->
    ident >>= (fun x -> 
      (* try (parens expr *> (return @@ Func (x, sep_by comma expr))) *)
      (* try (parens (return @@ Func (x, sep_by comma expr))) *)
      (parens (sep_by comma expr) >>= (fun terms -> return @@ Func (x, terms)))
      <|> (return @@ Var x)
    )
  )

let parser_atom : string atom t =
  ident >>= (fun x ->
    parens (sep_by comma parser_term) >>= (fun terms -> return @@ Pred (x, terms))
  )

let parser_lit : string literal t =
  eat_spaces *> 
  parse_tilde >>= (fun sign ->
    parser_atom >>= (fun lit ->
      return {sign; lit}
    )
  )

let parser_clause : string clause t =
  (* s |> String.split_on_char ',' |> List.map parser_lit *)
  sep_by (eat_spaces *> char ',' <* eat_spaces) parser_lit

let parser_clauseset : string clauseset t =
  sep_by (eat_spaces *> char '\n' <* eat_spaces) parser_clause

let parse s = 
  (* match parse_string parser_lit s with *)
  match parse_string parser_clauseset s with
  | Ok res -> List.filter (neg List.is_empty) res
  | Error msg -> failwith msg
