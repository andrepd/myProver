open Batteries

open Types
open Util

type 'a subst = 'a Subst.map

let rec istriv (env: 'a subst) x t = 
  match t with
  | Var y ->
    y = x || Map.mem y env && istriv env x (Map.find y env)
  | Func (name, args) ->
    List.exists (istriv env x) args && failwith "istriv: cyclic"

let rec unify (env: 'a subst) (eqs: ('a term * 'a term) list) : 'a subst = 
  match eqs with
  | [] -> env
  | (Func (f, fa), Func (g, ga))::xs ->
    if f = g && List.length fa = List.length ga then (* Compatible unification *)
      unify env (List.combine fa ga @ xs)
    else
      failwith "unify: impossible unification"
  | (Var x,t)::xs | (t,Var x)::xs ->
    if Map.mem x env then
      unify env ((Map.find x env, t)::xs)
    else
      let env' = 
        if istriv env x t then 
          env
        else 
          Map.add x t env
      in
      unify env' xs

let rec reduce (env: 'a subst) : 'a subst = 
  let env_func = Subst.map_to_func env in
  let env' = Map.map (Term.subst env_func) env in
  if env' = env then env else reduce env'

let mgu_list x = 
  (reduce @@ unify Map.empty x) |> Subst.map_to_func

let mgu x = mgu_list @@ List.singleton x

let mgu_list_map x =
  reduce @@ unify Map.empty x

let mgu_map x = mgu_list_map [x]
