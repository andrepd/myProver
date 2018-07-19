open Batteries

open Angstrom
open Types

(* Helpers *)

let whitespace x = 
  match x with
  | ' ' | '\t' | '\n' -> true
  | _ -> false

let eat_spaces = skip_while whitespace

let sp p = eat_spaces *> p

let parse_tilde = 
  char '~' *> return false
  <|> return true

(* let ident = eat_spaces *> take_while1 (function 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false)  *)
let ident = 
  let rest = ref false in
  eat_spaces *>
  take_while1 (function 'a'..'z' | 'A'..'Z' | '_' -> true | '0' .. '9' -> if !rest then true else (rest:=true; false) | _ -> false)

let parens p = char '(' *> p <* char ')'

let comma = char ','

let pred_op = eat_spaces *> choice [ 
  string "="; 
  string "<"; 
  string ">"]

let chainl1 e op =
  let rec go acc =
    (lift2 (fun f x -> f acc x) op e >>= go) <|> return acc in
  e >>= fun init -> go init

(* Main parsers *)
(* CNF *)

let parser_term : string term t =
  fix (fun expr ->
    ident >>= fun x -> 
    (
      (
        parens (sep_by (eat_spaces *> comma) expr) >>| fun terms -> 
          Func (x, terms)
      ) <|> (
        return @@ Var x
      )
    )
  )

let parser_atom : (bool * string atom) t =
  eat_spaces *> (
    (
      parser_term >>= fun x ->
      pred_op     >>= fun op ->
      parser_term >>| fun y ->
        (true, Pred (op, [x;y]))
    ) <|> (
      parse_tilde >>= fun sign ->
      ident >>= fun x ->
      parens (sep_by (eat_spaces *> comma) parser_term) >>| fun terms -> 
        (sign, Pred (x, terms))
    )
  )

let parser_lit : string literal t =
  eat_spaces *> 
  parser_atom >>| fun (sign, lit) ->
    {sign; lit}

let parser_clause : string clause t =
  sep_by (eat_spaces *> char ',') parser_lit

let parser_clauseset : string clauseset t =
  sep_by (eat_spaces *> char ';') parser_clause

let parse_cnf s = 
  match parse_string (eat_spaces *> parser_clauseset) s with
  | Ok res -> List.filter (neg List.is_empty) res
  | Error msg -> failwith msg

(* --- Full formula --- *)

let parser_val = 
  eat_spaces *> (
    (
      (string "T" <|> string "⊤") *> (return @@ Val true )
    ) <|> (
      (string "F" <|> string "⊥") *> (return @@ Val false)
    )
    (* <?> "Error literalTerm" *)
  )

let op_comma = eat_spaces *> (string ",") *> return (fun x y -> Or (x,y))
let op_colon = eat_spaces *> (string ";") *> return (fun x y -> And (x,y))

let op_and = eat_spaces *> (string "&"  <|> string "∧") *> return (fun x y -> And (x,y))
let op_or  = eat_spaces *> (string "|"  <|> string "∨") *> return (fun x y -> Or  (x,y))
let op_imp = eat_spaces *> (string "=>" <|> string "⇒") *> return (fun x y -> Imp (x,y))
let op_iff = eat_spaces *> (string "==" <|> string "⇔") *> return (fun x y -> Iff (x,y))

let parser_predicate : string formula t =
  eat_spaces *> 
  parser_atom >>| fun (sign, x) -> 
    if sign then Atom x else Not (Atom x)

let rec parser_quantifier() : string formula t =
  eat_spaces *> (
    (
      (string "@" <|> string "∀") *>
      sep_by eat_spaces ident >>= fun vars ->
      eat_spaces *> char '.' *> eat_spaces *>
      parser_boolean() >>| fun body ->
        List.fold_right (fun x y -> Forall (x,y)) vars body
    ) <|> (
      (string "\\" <|> string "∃") *>
      sep_by eat_spaces ident >>= fun vars ->
      eat_spaces *> char '.' *> eat_spaces *>
      parser_boolean() >>| fun body ->
        List.fold_right (fun x y -> Exists (x,y)) vars body
    )
  )

and parser_boolean() : string formula t =
  fix (fun expr ->
    (* print_endline "trace"; *)
    let parens_expr_wrapper =
      parse_tilde >>= fun sign ->
      parens expr >>| fun form ->
      if sign then form else Not form
    in

    (parens_expr_wrapper <|> parser_val <|> parser_quantifier() <|> parser_predicate)
    |> (flip chainl1) (op_and)
    |> (flip chainl1) (op_or )
    |> (flip chainl1) (op_imp)
    |> (flip chainl1) (op_iff)
  )

let parser_formula : string formula t =
  eat_spaces *> parser_boolean()

let parser_file : string formula t =
  let clause_p = sep_by1 (eat_spaces *> string ",") (eat_spaces *> parser_boolean()) in
  let clauseset_p = sep_by1 (eat_spaces *> string ";") (eat_spaces *> clause_p) in

  List.reduce (fun x y -> And (x,y)) <$> (
    List.map (
      List.reduce (fun x y -> Or (x,y))
    ) <$> clauseset_p
  )



let parse_formula s =
  match parse_string parser_formula s with
  | Ok res -> res
  | Error msg -> failwith msg

let parse_file f = 
  let strip_comments s = 
    try
      String.split s "#" |> fst
    with
    | Not_found -> s
  in

  let f = 
    f
    |> String.split_on_char '\n'
    |> List.map (String.trim % strip_comments)
    |> List.filter (neg String.is_empty) 
    |> String.concat ""
    |> tap print_endline
    (* |> parse_formula *)
  in

  match parse_string parser_file f with
  | Ok res -> res
  | Error msg -> failwith msg
