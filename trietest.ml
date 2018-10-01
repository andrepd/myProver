open Batteries

open Types

let index_of x l =
  List.findi (fun _ c -> c = x) l |> fst

let () = 
  let tree = Trie.create() in
  (* Trie.insert Func("F", [Func("A", [Var "x"])]) *)
  let list = [
    ((Pred (2, [Func(2,  [Var (-1);   Var(-2)   ])])), "a");
    ((Pred (2, [Func(2,  [Var (-1);   Func(3,[])])])), "b");
    ((Pred (2, [Func(4,  [Var (-1);   Func(3,[])])])), "c");
    ((Pred (2, [Func(2,  [Func(9,[]); Var (-1)  ])])), "c'");
    ((Pred (1, [Func(2,  [Var (-1);   Func(3,[])])])), "d");
    ((Pred (1, [Func(2,  [Func(2,[]); Func(3,[])])])), "e");
    ((Pred (1, [Func(2,  [Func(2,[]); Func(2,[])])])), "f");
    ((Pred (3, [Func(22, [])                      ])), "g");
    ((Pred (3, [Func(23, [])                      ])), "h");
    ((Pred (3, [Var(-3)                           ])), "i");
    ((Pred (4, [])), "j");
    ((Pred (2, [Func(2,  [Func(9,[]); Func(4,[])   ])])), "a'");

    ((Pred (2, [Func(2,  [Func(9,[]); Func(4,[])   ])])), "2a");
    ((Pred (2, [Func(2,  [Func(9,[]); Func(4,[])   ])])), "2a");
  ]
  in
  let tree = List.fold_left (fun x y -> Trie.insert x (fst y) (snd y)) tree list
  in

  (* print_int @@ List.length @@ Trie.unifiable tree ((Func (1, [Func(2, [Var (-1);Func(3,[])])])));
  print_int @@ List.length @@ Trie.unifiable tree ((Func (1, [Func(4, [Var (-1);Func(3,[])])]))); *)
  List.iter (fun (x,_) ->
    (* print_int % List.length @@ Trie.unifiable tree x; print_newline() *)
    (* print_endline @@ String.concat "," @@ List.map string_of_int @@ (List.map (fun x -> index_of x list) @@ Trie.unifiable tree x)(* ; print_newline() *) *)

    let unifiables = List.map snd @@ Trie.unifiable tree x in
    print_endline @@ String.concat "," unifiables
  ) list;

  ()
