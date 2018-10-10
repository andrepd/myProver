open Types

type assignment = bool list list

(** Map variables to elem *)
val abstraction : elem:'a -> 'a clauseset -> 'a clauseset

(** Check propositional satisfiability of clauseset, and return propositional assignment, if any *)
val satisfiable : elem:'a -> 'a clauseset -> assignment option
