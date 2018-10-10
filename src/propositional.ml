open Batteries

open Types
open Util
open Debug

type solver = 
  | Minisat
  | MyDPLL

let solver = Minisat


type assignment = bool list list

type numbering = int List.t List.t * (int*int)

(* let numbering (x: 'a clauseset) : int LazyList.t LazyList.t * (int*int) = *)
let numbering (x: 'a clauseset) : numbering =
  let store = ref Map.empty in
  let num = ref 1 in
  
  let clauses = 
    x |> List.map (fun clause ->
      clause |> List.map (fun {sign;atom} -> 
        let n =
          try
            Map.find atom !store
          with
            Not_found -> (
              store := Map.add atom !num !store;
              incr num;
              !num-1
            )
        in
        if sign then n else -n
      )
    )
  in
  let nvars = !num-1 in
  let nclauses = List.length clauses in
  (clauses,(nvars,nclauses))

(* let numbering_to_pcnf (x: numbering) : string = *)
let numbering_to_pcnf ((clauses,(nvars,nclauses)): numbering) : string =
  let body = Buffer.create ((nvars * 4) * nclauses) in
  Buffer.add_string body "p cnf ";
  Buffer.add_string body (Int.to_string nvars);
  Buffer.add_char   body (' ');
  Buffer.add_string body (Int.to_string nclauses);
  Buffer.add_char   body ('\n');
  List.iter (fun clause ->
    List.iter (fun n -> 
      Buffer.add_string body (Int.to_string n);
      Buffer.add_char body ' '
    ) clause;
    Buffer.add_string body "0\n"
  ) clauses;
  Buffer.contents body
  
let to_pcnf (x: 'a clauseset) : string =
  x |> numbering |> numbering_to_pcnf

type pmodel = bool array

let call_mydpll (str: string) : pmodel option =
  if dbg_flag then begin  
  debug_endline "FILE";
  debug_string str;
  debug_endline "ENDFILE";
  end;
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
  (* let status = Unix.close_process_full (out_chan, in_chan, err_chan) in *)

  let process_model s =
    let l = String.split_on_char ' ' s |> List.map String.trim |> List.filter (neg String.is_empty) in
    (* debug_int (List.length l); *)
    let a = Array.make (List.length l) false in
    List.iter (fun x ->
      try
        let x = Int.of_string x in
        let sign = x>0 in
        let atom = abs(x) in
        a.(atom-1) <- sign
      with Failure _ ->
        ()
    ) l;
    a
  in

  if dbg_flag then begin
  debug_endline sat;
  end;
  if sat.[0] = 'S' then (  (* WAS== *)
    if dbg_flag then begin
    debug_string model
    end;
    Some (process_model model)
  ) else
    None

let call_minisat (str: string) : pmodel option =
  if dbg_flag then begin  
  debug_endline "FILE";
  debug_string str;
  debug_endline "ENDFILE";
  end;
  let fin = File.open_out "sattmp.in" in
  IO.nwrite fin str;
  IO.close_out fin;
  let out_chan = Unix.open_process_in "./external_bin/minisat sattmp.in sattmp.out" in
  ignore @@ IO.read_all out_chan;
  let fout = File.open_in "sattmp.out" in
  let sat   = IO.read_line fout in
  let sat   = sat.[0] = 'S' in
  let model = if sat then IO.read_line fout else "" in
  IO.close_in fout;

  (* let process_model s =
    let l = String.split_on_char ' ' s |> List.map String.trim |> List.filter (neg String.is_empty) in
    let a = Array.make (List.length l) false in
    List.iter (fun x ->
      try
        let x = Int.of_string x in
        if x <> 0 then (
          let sign = x>0 in
          let atom = abs(x) in
          a.(atom-1) <- sign
        )
      with Failure _ ->
        ()
    ) l;
    a
  in *)

  let process_model s =
    (* let open Angstrom in
    let p_space = function ' ' -> true | _ -> false in
    let p_var = 
    let p_model = sep_by p_space p_var *)

    let l = String.split_on_char ' ' s in
    (* List.print ~first:"[`" ~last:"`]\n" ~sep:"`;`" String.print stderr l; *)

    let a = 
      List.enum l
      |> Enum.take_while (fun x -> x.[0] <> '0')
      |> Enum.map (fun x -> x.[0] <> '-')
      |> Array.of_enum
    in
    a

    (* Array.make (List.length l) false in
    List.iter (fun x ->
      try
        let x = Int.of_string x in
        if x <> 0 then (
          let sign = x>0 in
          let atom = abs(x) in
          a.(atom-1) <- sign
        )
      with Failure _ ->
        ()
    ) l;
    a *)
  in

  if dbg_flag then begin
  debug_endline @@ if sat then "SAT" else "UNSAT";
  end;
  (* if sat.[0] = 'S' then (  (* WAS== *) *)
  if sat then (
    if dbg_flag then begin
    debug_string model
    end;
    Some (process_model model)
  ) else
    None

let call_sat_solver = 
  match solver with
  | Minisat -> call_minisat
  | MyDPLL -> call_mydpll


(** Map variables to elem *)
let abstraction ~(elem: 'a) (x: 'a clauseset) = 
  Clauseset.subst (fun x -> Func (elem,[])) x

(* let pcnf : (string * string) =

let add_pcnf

let pncf_to_text (header, body) =
  header ^ body *)

(** Check propositional satisfiability of clauseset, and return propositional assignment, if any *)
let satisfiable ~(elem: 'a) (x: 'a clauseset) : assignment option = 
  let abstraction = abstraction elem x in
  let numbering = numbering abstraction in
  let pcnf = numbering_to_pcnf numbering in
  (* debug_endline pcnf; *)

  match call_sat_solver pcnf with
  | Some model -> (
    (* Array.iter (function true -> debug_string "T " | false -> debug_string "F ") model; debug_newline(); *)
    let sign x = x > 0 in
    let aux = fun x -> let x' = abs(x)-1 in model.(x') = sign x in
    let assignments = List.map (List.map aux) (fst numbering) in
    Some assignments
  )
  | None -> None
