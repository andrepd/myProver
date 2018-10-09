open Batteries

open Types

let ($) = (@@)

(* Conversion functions *)
let lit_to_func x =
  let {sign; atom=Pred(name, args)} = x in
  let sign_name = if sign then "T" else "F" in
  Func(sign_name, [Func(name, args)])

let func_to_lit x =
  let Func(sign_name, [Func(name, args)]) = x in
  let sign = sign_name = "T" in
  {sign; atom=Pred(name, args)}

(* Helper function *)
module ListEx = struct
  include List
  let rec assoc_add (a: 'a) (b: 'b) (l: ('a*'b) list) : ('a*'b) list = 
    match l with
    | [] -> [(a,b)]
    | ((g,h) as x)::xs -> (
      if g = a then
        (a,b) :: xs
      else
        x :: assoc_add a b xs
    )
end
module List = ListEx

(* --- *)

(* 
{sign=false; atom=Pred('P',[Func('a',[]);Func('b',[])])}
=>
Func('$F',[Func('P',[Func('a',[]);Func('b',[])])])
*)

(* 
Node [
  f, Node [
    *, Node [
      *, Leaf [..]
    ]
    a, Node []
    g,  
]
*)

type ('a,'c) entry = {
  term: ('a,'c) tree;
  arity: int; 
}

and ('a,'c) tree = 
  | Node of ('a * ('a,'c) entry) list
  | Leaf of ('c) list
  (* | Nil *)

let pred_to_term (Pred(name,args)) = Func(name,args)
let term_to_pred (Func(name,args)) = Pred(name,args)

module Term = struct
  type 'c t = (int, 'c) tree

  let create() = 
    Node []

  (* let next tree x = 
    let open Option.Infix in
    match tree with
    (* | Node l -> List.assoc_opt x l >>= snd *)
    | Node l -> Option.map snd $ List.assoc_opt x l
    | Leaf _ -> None *)

  let next l x = 
    Option.map (fun {term;_} -> term) $ List.assoc_opt x l

  let skip tree =
    let rec aux tree n =
      match tree with
      | Node l -> (
        if n = 0 then 
          [tree]
        else
          List.concat $ List.map (fun (_, {term;arity}) -> aux term (n-1 + arity)) l
      )
      (* | Leaf _ -> failwith "skip: should not happen" (* [] *) *)
      | Leaf _ -> [tree]
    in
    match tree with
    | Node l -> (
      List.concat $ List.map (fun (_, {term;arity}) -> aux term arity) l
    )
    | Leaf _ -> failwith "skip: should not happen" (* [] *)

  let insert tree index payload : 'a t =
    let rec aux (tree: 'a t) (terms: int term list) (payload: 'a) : 'a t =
      match (tree, terms) with
      | Node l, (Var x)::xs -> (
        let child : 'a t = next l 0 |? create() in
        let child' : 'a t = aux child xs payload in
        let arity = 0 in
        Node (List.assoc_add 0 {term=child'; arity} l)
      )
      | Node l, (Func(name, args))::xs -> (
        let child : 'a t = next l name |? create() in
        let child' : 'a t = aux child (args@xs) payload in
        let arity = List.length args in
        Node (List.assoc_add name {term=child'; arity} l)
      )
      | Node [], [] -> (
        Leaf [payload]
      )
      | Leaf l, [] -> (
        (* Check if not duplicate (actually nevermind) *)
        Leaf (payload::l)
      )
      | Node (_::_), [] -> failwith "insert: should not happen (nonempty node with empty list)"
      | Leaf _, (_::_) -> failwith "insert: should not happen (leaf with nonempty list)"
    in
    aux tree [index] (payload)

  (* let delete tree t : 'a t =
    let rec aux (tree: 'a t) (terms: int term list) (t) : 'a t =
      match (tree, terms) with
      | Node l, (Var x)::xs -> (
        let child : 'a t = next l 0 |? create() in
        let child' : 'a t = aux child xs t in
        let arity = 0 in
        Node (List.assoc_add 0 {term=child'; arity} l)
      )
      | Node l, (Func(name, args))::xs -> (
        let child : 'a t = next l name |? create() in
        let child' : 'a t = aux child (args@xs) t in
        let arity = List.length args in
        Node (List.assoc_add name {term=child'; arity} l)
      )
      | Node [], [] -> (
        Leaf [t]
      )
      | Leaf l, [] -> (
        (* Check if not duplicate (actually nevermind) *)
        Leaf (t::l)
      )
      | Node (_::_), [] -> failwith "insert: should not happen (nonempty node with empty list)"
      | Leaf _, (_::_) -> failwith "insert: should not happen (leaf with nonempty list)"
    in
    aux tree [t] t *)

  let unifiable tree x =
    let rec aux tree terms = 
      match (tree, terms) with
      (* | (Nil, _) -> [] *)
      | (Leaf l, []) -> l
      | (Node l, (Var x)::xs) ->
        List.concat $ List.map (fun x -> aux x xs) (skip tree) (* OOPSIE *) (* AI NAO TÁ BEM *)
        (* List.concat $ List.map (fun x -> aux x xs) (skip l) *)
      | (Node l, (Func(name, args))::xs) -> 
        (* aux (Option.get $ next l 0) xs
        @
        aux (Option.get $ next l name) (args @ xs) *)
        (match next l 0    with Some child -> aux child xs          | None -> [])
        @
        (match next l name with Some child -> aux child (args @ xs) | None -> [])
      | (Node _, []) -> failwith "unifiable: shouldn't happen (node with empty list)"
      | (Leaf _, _::_) -> failwith "unifiable: shouldn't happen (leaf with nonempty list)"
    in
    aux tree [x]
end

module Atom = struct
  type 'c t = (int, 'c) tree

  let create() = 
    Node []

  let insert tree index payload = 
    Term.insert tree (pred_to_term index) payload 

  let unifiable tree x = 
    Term.unifiable tree (pred_to_term x)
end

module Literal = struct
  type 'c t = {
    pos: 'c Atom.t;
    neg: 'c Atom.t;
  }

  let create() = {
    pos = Atom.create();
    neg = Atom.create();
  }

  let insert tree {sign;atom=atom} payload =
    if sign then 
      {tree with pos = Atom.insert tree.pos atom payload}
    else
      {tree with neg = Atom.insert tree.neg atom payload}

  let unifiable tree {sign;atom=atom} =
    if sign then
      Atom.unifiable tree.neg atom
    else
      Atom.unifiable tree.pos atom
end
