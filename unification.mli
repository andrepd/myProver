open Types

val mgu : 'a term * 'a term -> ('a -> 'a term)
(** Returns the mgu of two terms. If not possible, raises [Failure] *)

val mgu_list : ('a term * 'a term) list -> ('a -> 'a term)
(** Returns the mgu of a list of terms. If not possible, raises [Failure] *)
