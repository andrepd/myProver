(** Represents a first-order formula, with boolean connectives: not, and, or, implies, iff *)
type 'a t = 
  | Val of bool
  | Atom of 'a Atom.t
  | Not of 'a t
  | And of 'a t * 'a t
  | Or  of 'a t * 'a t
  | Imp of 'a t * 'a t
  | Iff of 'a t * 'a t
  | Forall of 'a * 'a t
  | Exists of 'a * 'a t

(** S-expression representation of a formula *)
val to_string : ('a -> string) -> 'a t -> string  (* lift monad *)

(** Prints s-expression representation of a formula to an output*)
(* val print : 
  ('a BatInnerIO.output -> 'b -> unit) ->
  'a BatInnerIO.output -> 
  'b t -> 
  unit *)

(** [subst variant] will apply a substitution (mapping of variables to terms) to a formula, where [variant] is a function ['a -> 'a list -> 'a] that takes an identifier and a list of identifiers and returns a fresh one not in that list *)
val subst : variant:('a -> 'a list -> 'a) -> ('a -> 'a Term.t) -> 'a t -> 'a t 

(** List of functions (as (name,arity)) in a formula, including duplicates *)
val list_functions : 'a t -> ('a * int) list 

(** List of predicates (as (name,arity)) in a formula, including duplicates *)
val list_predicates : 'a t -> ('a * int) list 

(** List of variables in a formula, with no duplicates *)
val list_vars : 'a t -> 'a list

(** As [list_vars] *)
val vars : 'a t -> 'a list

(** List of free variables in a formula, with no duplicates *)
val free_vars : 'a t -> 'a list
