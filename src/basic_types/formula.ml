open Batteries

let ($) = (@@)

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

(* type 'a t = 'a formula *)

type 'a formula = 'a t

let rec to_string inner x =
  match x with
  | Val true -> "$T"
  | Val false -> "$F"
  | Atom x -> Atom.to_string inner x
  | Not x -> "(NOT " ^ to_string inner x ^ ")"
  | And (x,y) -> "(AND " ^ to_string inner x ^ " " ^ to_string inner y ^ ")"
  | Or  (x,y) -> "(OR " ^ to_string inner x ^ " " ^ to_string inner y ^ ")"
  | Imp (x,y) -> "(IMP " ^ to_string inner x ^ " " ^ to_string inner y ^ ")"
  | Iff (x,y) -> "(IFF " ^ to_string inner x ^ " " ^ to_string inner y ^ ")"
  | Forall (x, p) -> "(FORALL " ^ inner x ^ " " ^ to_string inner p ^ ")"
  | Exists (x, p) -> "(EXISTS " ^ inner x ^ " " ^ to_string inner p ^ ")"

(* --- Organize *)

let (|=>) a b x = 
  if x = a then b else Term.Var x

let (|->) a b f x = 
  if x = a then b else f x

let vars_term (t: 'a Term.t) =
  let open Term in
  let rec aux t =
    match t with
    | Var x -> [x]
    | Func (_, args) -> List.concat $ List.map aux args
  in 
  List.sort_unique compare @@ aux t

let vars (f: 'a formula) =
  let rec aux f =
    match f with
    | Val _ -> []
    | Atom (Pred (_, args)) -> List.concat $ List.map vars_term args
    | Not x -> aux x
    | And (x,y) | Or (x,y) | Imp (x,y) | Iff (x,y) -> 
      aux x @ aux y
    | Forall (x, p) | Exists (x, p) -> 
      List.cons x (aux p)
  in
  List.sort_unique compare @@ aux f

let rec free_vars (f: 'a formula) = 
  let rec aux f =
    match f with
    | Val _ -> []
    | Atom (Pred (_, args)) -> List.concat $ List.map vars_term args
    | Not x -> aux x
    | And (x,y) | Or (x,y) | Imp (x,y) | Iff (x,y) -> 
      aux x @ aux y
    | Forall (x, p) | Exists (x, p) -> 
      (* List.remove (aux p) x *)
      List.remove (free_vars p) x  (* ######################## *)
  in
  aux f |> List.sort_unique compare

(* --- *)

let subst ~variant s f =
  let rec subst' (s: 'a Subst.fn) (f: 'a formula) =
    let needs_rename x p = 
      List.exists (fun y -> List.mem x (vars_term $ s y)) (free_vars $ Forall (x,p))
    in

    match f with 
    | Val _ -> f
    | Atom x -> Atom (Atom.subst s x)
    | Not x -> Not (subst' s x)
    | And (x,y) -> And (subst' s x, subst' s y)
    | Or  (x,y) -> Or  (subst' s x, subst' s y)
    | Imp (x,y) -> Imp (subst' s x, subst' s y)
    | Iff (x,y) -> Iff (subst' s x, subst' s y)
    | Forall (x, p) -> (
      if s x <> Var x then
        failwith "Formula.subst: cannot replace bound var"
      else if needs_rename x p then (
        let x' = variant x (free_vars p) in
        Forall (x', subst' ((x |-> Term.Var x') s) p)
      ) else (
        Forall (x, subst' s p)
      )
    )
    | Exists (x, p) -> (
      if s x <> Var x then
        failwith "Formula.subst: cannot replace bound var"
      else if needs_rename x p then (
        let x' = variant x (free_vars p) in
        Exists (x', subst' ((x |-> Term.Var x') s) p)
      ) else (
        Exists (x, subst' s p)
      )
    )
  in
  subst' s f

let list_functions (x: 'a formula) : ('a * int) list =
  let rec aux (f: 'a formula) : ('a * int) list =
    match f with
    | Val x -> []
    | Atom x -> Atom.list_functions x
    | Not x -> aux x
    | And (x,y) | Or (x,y) | Imp (x,y) | Iff (x,y) ->
      aux x @ aux y
    | Forall (_, p) | Exists (_, p) ->
      aux p
  in
  (* List.sort_unique compare @@  *)
  aux x

let list_predicates (x: 'a formula) : ('a * int) list =
  let rec aux (f: 'a formula) : ('a * int) list =
    match f with
    | Val x -> []
    | Atom x -> Atom.list_predicates x
    | Not x -> aux x
    | And (x,y) | Or (x,y) | Imp (x,y) | Iff (x,y) ->
      aux x @ aux y
    | Forall (_, p) | Exists (_, p) ->
      aux p
  in
  (* List.sort_unique compare @@  *)
  aux x

let list_vars x = vars x
