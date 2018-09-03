open Batteries

open Types
open Util

open Debug

let bold x = "\o033[1m" ^ x ^ "\o033[0m"

let sign x = x>0

(* ---- *)






let test_cnf() =
  let input = IO.read_all stdin in

  print_endline @@ bold "Original formula:";
  let test_formula = Parser.parse_cnf input in
  print_endline @@ string_of_clauseset test_formula;
  print_newline();
  
  print_endline @@ bold "Encoded formula:";
  let encoded_formula = Util.encode_clauseset test_formula in
  print_endline @@ string_of_int_clauseset encoded_formula;
  print_newline();

  print_endline @@ bold "Propositional abstraction:";
  let designated = 
    list_functions_clauseset encoded_formula
    |> List.filter (fun x -> snd x = 0)
    |> List.shuffle
    |> List.hd |> fst
  in
  print_endline @@ string_of_int designated;
  (* let prop_formula = prop_abstraction 0 encoded_formula in *)
  let prop_formula = InstGen.prop_abstraction designated encoded_formula in
  print_endline @@ string_of_int_clauseset @@ prop_formula;
  print_newline();
  
  print_endline @@ bold "pcnf text:";
  print_string @@ to_pcnf prop_formula;
  print_newline();
  
  print_endline @@ bold "Prop satisfiability of above:";
  (* let sat = check_prop_satisfiability 0 prop_formula in *)
  (* let sat = check_prop_satisfiability 0 encoded_formula in *)
  let sat = InstGen.check_prop_satisfiability designated encoded_formula in
  print_endline @@ (match sat with Some _ -> "SAT" | None -> "UNSAT");
  print_newline();

  (* print_endline "Starting instance generation";
  let new_instances = inst_gen test_formula in
  print_endline "Done";

  begin match new_instances with
  | Some x -> 
    print_endline @@ string_of_clauseset x
  | None ->
    print_endline "None found"
  end; (* SEM O END PENSA QUE O RESTO TÁ DEBAIXO DO NONE *)
  print_newline(); *)

  let sat = InstGen.main_loop encoded_formula in
  print_endline @@ if sat then "FOL SAT" else "FOL UNSAT";

  ()



let test_formula() =
  let input = IO.read_all stdin in

  print_endline @@ bold "Input:";
  print_endline input;

  print_endline @@ bold "Original formula:";
  let test_formula = Parser.parse_file input in
  print_endline @@ string_of_formula test_formula;
  print_newline();
  
  print_endline @@ bold "Skolemized:";
  (* let skolem_formula = Clausification.skolemize (Not test_formula) in *)
  let skolem_formula = Clausification.skolemize (test_formula) in
  print_endline @@ string_of_formula skolem_formula;
  print_newline();
  
  print_endline @@ bold "CNF:";
  let cnf_formula = Clausification.clausify skolem_formula in
  print_endline @@ string_of_clauseset cnf_formula;
  print_newline();
  
  print_endline @@ bold "Equality axioms:";
  let eq_axioms = Equality.axioms_string cnf_formula in
  print_endline @@ string_of_clauseset eq_axioms;
  print_newline();
  
  (* print_endline @@ bold "Optimized CNF:";
  let cnf_formula = Clausification.clausify_opt test_formula in
  print_endline @@ string_of_clauseset cnf_formula;
  print_newline(); *)
  
  let full_formula = 
    if List.mem ("=",2) (list_predicates_clauseset cnf_formula ) then (
      print_endline "Adding equality axioms.";
      cnf_formula @ eq_axioms
    ) else (
      print_endline "Won't add equality axioms.";
      cnf_formula
    )
  in
  let sat = InstGen.main_loop @@ Util.encode_clauseset full_formula in
  print_endline @@ if sat then "FOL SAT" else "FOL UNSAT";

  ()



let () = test_formula()
