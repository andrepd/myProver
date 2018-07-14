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

let ident = eat_spaces *> take_while1 (function 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false) 

let parens p = char '(' *> p <* char ')'

let comma = char ','

let pred_op = eat_spaces *> choice [string "="]

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

let parser_atom : string atom t =
  eat_spaces *> (
    (
      parser_term >>= fun x ->
      pred_op     >>= fun op ->
      parser_term >>| fun y ->
        Pred (op, [x;y])
    ) <|> (
      ident >>= fun x ->
      parens (sep_by (eat_spaces *> comma) parser_term) >>| fun terms -> 
        Pred (x, terms)
    )
  )

let parser_lit : string literal t =
  eat_spaces *> 
  parse_tilde >>= fun sign ->
  parser_atom >>| fun lit ->
    {sign; lit}

let parser_clause : string clause t =
  sep_by (eat_spaces *> char ',') parser_lit

let parser_clauseset : string clauseset t =
  sep_by (eat_spaces *> char ';') parser_clause

let parse_cnf s = 
  match parse_string (eat_spaces *> parser_clauseset) s with
  | Ok res -> List.filter (neg List.is_empty) res
  | Error msg -> failwith msg

(* Full formula *)
let parser_val = 
  eat_spaces *> (
        (string "T" *> (return @@ Val true ))
    <|> (string "F" *> (return @@ Val false))
    <|> (string "⊤" *> (return @@ Val true ))
    <|> (string "⊥" *> (return @@ Val false))
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
  parse_tilde >>= fun sign ->
  parser_atom >>| fun x -> 
    if sign then Atom x else Not (Atom x)

(* let parser_boolean : string formula t = 
  return @@ Atom (Pred ("ERROR", [])) *)

let rec parser_quantifier() : string formula t =
  (* fix (fun expr ->  *)
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
  (* ) *)

and parser_boolean() : string formula t =
  fix (fun expr ->
    (* print_endline "trace1"; *)
    (* let level1 = parens expr <|> parser_val <|> parser_quantifier() <|> parser_predicate in
    let level2 = chainl1 level1 (op_and) in
    let level3 = chainl1 level2 (op_or ) in
    let level4 = chainl1 level3 (op_imp) in
    let level5 = chainl1 level4 (op_iff) in

    let level6 = chainl1 level5 (op_comma) in
    let level7 = chainl1 level6 (op_colon) in

    level7 *)

    (parens expr <|> parser_val <|> parser_quantifier() <|> parser_predicate)
    |> (flip chainl1) (op_and)
    |> (flip chainl1) (op_or )
    |> (flip chainl1) (op_imp)
    |> (flip chainl1) (op_iff)
  )

let parser_formula : string formula t =
  (* eat_spaces *> parser_boolean() *)
  let clause_p = sep_by1 (string ",") (eat_spaces *> parser_boolean()) in
  let clauseset_p = sep_by1 (string ";") (eat_spaces *> clause_p) in
  (* List.map <$> (
    List.reduce (lift2 @@ fun x y -> Or (x,y))
  ) clauseset_p
  |> List.reduce (lift2 @@ fun x y -> And (x,y)) *)
  (* List.map () <$> clauseset_p *)
  List.reduce (fun x y -> And (x,y)) <$> (
    List.map (
      List.reduce (fun x y -> Or (x,y))
    ) <$> clauseset_p
  )
  (* |> List.reduce (fun x y -> And (x,y)) *)

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
  let lines =
    String.split_on_char ';' f 
    (* |> List.filter (neg @@ (flip String.starts_with) "#") *)
    (* |> List.map ((flip String.split) "#" |> fst) *)
    |> List.map strip_comments
    |> List.filter (neg String.is_empty) 
  in
  print_int @@ List.length lines;
  let formulae = List.map (parse_string parser_formula) lines in
  (* let okay = not @@ List.exists Option.is_none formulae in 
  if okay then
    List.reduce (fun x y -> And (x,y))
  else
    failwith *)
  let error = List.find_opt (function Error _ -> true | Ok _ -> false) formulae in 
  match error with
  (* | None -> List.reduce (fun x y -> And (x,y)) @@ List.map Legacy.Pervasives.(fun (Ok x) -> x) formulae *)
  | None -> List.reduce (fun x y -> And (x,y)) @@ List.map (fun x -> match x with Error _ -> assert false | Ok x -> x) formulae
  | Some (Error msg) -> failwith msg
