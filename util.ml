open Batteries

open Types

let rec subst_term (s: 'a -> 'a term) (f: 'a term) =
  match f with
  | Var x -> s x
  | Func (name, args) -> Func (name, List.map (subst_term s) args)

let subst_atom (s: 'a -> 'a term) (f: 'a atom) =
  let Pred (name, args) = f in Pred (name, List.map (subst_term s) args)

let subst_literal (s: 'a -> 'a term) ({sign; lit}: 'a literal) = 
  {sign; lit=subst_atom s lit}

let subst_clause (s: 'a -> 'a term) (f: 'a clause) =
  List.map (subst_literal s) f

let subst_clause_set (s: 'a -> 'a term) (f: 'a clauseset) =
  List.map (subst_clause s) f

let to_pcnf (x: 'a clauseset) : string =
  let store = ref @@ Map.empty in
  let num = ref 1 in
  let body = ref "" in
  List.iter (fun clause ->
    List.iter (fun {sign;lit} -> 
      let n =
        try
          Map.find lit !store
        with
          Not_found -> (
            store := Map.add lit !num !store;
            incr num;
            !num-1
          )
      in
      if sign then
        body := !body ^ Int.to_string n ^ " "
      else
        body := !body ^ "-" ^ Int.to_string n ^ " "
    ) clause;
    body := !body ^ "0\n"
  ) x;
  let header = "p cnf " ^ Int.to_string (!num-1) ^ " " ^ Int.to_string (List.length x) ^ "\n" in
  header ^ !body

let call_sat_solver (str: string) : pmodel option =
  (* let in_descr = Unix.descr_of_in_channel @@ IO.input_string str in
  let out_descr = Unix.descr_of_out_channel @@ IO.output_string () in
  let pid = Unix.create_process "./sat" [||] in_descr out_descr Unix.stderr in *)
  let out_chan, in_chan, err_chan = Unix.open_process_full "./sat" [||] in
  IO.nwrite in_chan str;
  IO.flush in_chan;
  (* IO.read out_chan = 'S' *)
  (* let sat = IO.nread out_chan (1024*4) in *)
  let sat = IO.read_all out_chan in
  (* let model = IO.nread err_chan (1024*4) in *)
  let model = IO.read_all err_chan in
  let status = Unix.close_process_full (out_chan, in_chan, err_chan) in

  (* let process_model s =
    String.split_on_char ' ' s
    (* |> List.map Int.of_string *)
    (* Array.init (List.length l) () *)
    |> List.map (fun x -> Int.of_string x > 0)
    |> Array.of_list
  in *)

  let process_model s =
    let l = String.split_on_char ' ' s in
    let a = Array.make (List.length l) false in
    List.iter (fun x ->
      try
        let x = Int.of_string x in
        let sign = x>0 in
        let lit = abs(x) in
        a.(lit-1) <- sign
      (* with Failure "int_of_string" -> *)
      with Failure _ ->
        ()
    ) l;
    a
  in

  (* print_endline sat;
  print_endline model; *)

  if sat.[0] == 'S' then
    (* Some (process_model @@ String.lchop ~n:12 res) *)
    Some (process_model model)
  else
    None
