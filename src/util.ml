open Batteries

open Types
open Debug

let ($) = (@@)

let (|=>) a b x = 
  if x = a then b else Var x

let (|->) a b f x = 
  if x = a then b else f x

(* --- *)

let string_of_int_subst s = Subst.to_string Int.to_string




let rec variant_string x l =
  if List.mem x l then 
    variant_string (x^"'") l
  else
    x

let rec variant_int x l =
  if List.mem x l then 
    variant_int (succ x) l
  else
    x 
