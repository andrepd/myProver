open Types

val parse_cnf : string -> string clauseset
(** Parses a formula in CNF: ';' delimited set of clauses, where each clause is a ',' delimited set of literals, where each literal is a predicate or its negation *)

val parse_formula : string -> string formula
(** Parses a formula in first-order logic. ',' is a synonym for OR, with lower priority, and ';' is a synonym for AND, with even lower priority *)

val parse_file : string -> string formula
(** Same as [parse_formula] but strips comments *)
