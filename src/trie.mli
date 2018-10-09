(* type ('a,'b) tree

val create : unit -> ('a,'b) tree

val insert : ('a,'b) tree -> 'b -> ('a,'b) tree

val unifiable : ('a,'b) tree -> 'b -> 'b list *)

(* OR *)

(* open Types

type 'a t

val create : unit -> 'a t

val insert : 'a t -> 'a term -> 'a t

val unifiable : 'a t -> 'a term -> 'a term list *)

(* OR *)

open Types

(* module type Term = sig *)
module Term : sig
	type 'a t

	val create : unit -> 'a t

	val insert : 'a t -> int term -> 'a -> 'a t

	val unifiable : 'a t -> int term -> 'a list

	(* val delete : 'a t -> int atom -> 'a t *)
end

(* module type Atom = sig *)
module Atom : sig
	type 'a t

	val create : unit -> 'a t

	val insert : 'a t -> int atom -> 'a -> 'a t

	val unifiable : 'a t -> int atom -> 'a list

	(* val delete : 'a t -> int atom -> 'a t *)
end

(* module type Literal = sig *)
module Literal : sig
	type 'a t

	val create : unit -> 'a t

	val insert : 'a t -> int literal -> 'a -> 'a t

	val unifiable : 'a t -> int literal -> 'a list

	(* val delete : 'a t -> int atom -> 'a t *)
end










(* module type Set = sig
  type t

  val create : unit -> t

  val insert : t -> int literal -> t

  val unifiable : t -> int literal -> int literal list
end *)

(* val term_to_pred : 'a term -> 'a atom

val pred_to_term : 'a atom -> 'a term *)
