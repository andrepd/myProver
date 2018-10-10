let dbg_flag = false

(* let debug_endline x = if dbg_flag then prerr_endline (Lazy.force x) (* x *)
let debug_string  x = if dbg_flag then prerr_string  (Lazy.force x) (* x *)
let debug_newline() = if dbg_flag then prerr_newline()
let debug_int     x = if dbg_flag then prerr_int     (Lazy.force x) (* x *) *)
let debug_endline x = prerr_endline x (* (Lazy.force x)  *)
let debug_string  x = prerr_string  x (* (Lazy.force x)  *)
let debug_newline() = prerr_newline()
let debug_int     x = prerr_int     x (* (Lazy.force x)  *)

let debug_printf = Printf.eprintf

let debug_out = stderr

(* OR *)

(* [%%define debug false]

(* [%%if debug = true] *)
let debug_endline x = prerr_endline x (* (Lazy.force x) *)
let debug_string  x = prerr_string  x (* (Lazy.force x) *)
let debug_newline() = prerr_newline()
let debug_int     x = prerr_int     x (* (Lazy.force x) *)
(* [%%else]
let debug_endline x = ()
let debug_string  x = ()
let debug_newline() = ()
let debug_int     x = ()
[%%endif] *) *)
