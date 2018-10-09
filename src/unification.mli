open Types

val mgu : 'a term * 'a term -> ('a -> 'a term)
(** Returns the mgu of two terms. If not possible, raises [Failure] *)

val mgu_list : ('a term * 'a term) list -> ('a -> 'a term)
(** Returns the mgu of a list of terms. If not possible, raises [Failure] *)

val mgu_map : 'a term * 'a term -> ('a, 'a term) BatMap.t
(** Like mgu, but returns a map instead of a term *)

val mgu_list_map : ('a term * 'a term) list -> ('a, 'a term) BatMap.t
(** Like mgu_list, but returns a map instead of a term *)

val map_to_func : ('a, 'a term) BatMap.t -> ('a -> 'a term) 
