open Lambda

module IntMap = Map.Make(Int)

type extpos = Down | Left | Right | Up

let pr_extpos = function
  | Down -> "↓"
  | Left -> "↙"
  | Right -> "↘"
  | Up -> "↑"

let calc_transition_system : pure_term -> int * (int * extpos * int) list =
  let rec aux curr vars trs = function
    | Lam t ->
      aux  (curr + 1) (push_debruijn vars curr) ((curr, Down, curr+1)::trs) t
    | Var i ->
      curr, (curr, Up, Option.get @@ find_debruijn vars i)::trs
    | App (t, u) ->
      let next, trs = aux (curr + 1) vars ((curr, Left,  curr+1)::trs) t in
      let next, trs = aux (next + 1) vars ((curr, Right, next+1)::trs) u in
      next, trs
  in aux 0 empty_debruijn []

type term =
  { id : int
  ; term : term termf }

let pr_term t =
  let rec aux (pos : pos) { id; term } =
    let parens t = "(" ^ t ^ ")" in
    match term with
    | Lam x ->
      let step = Printf.sprintf "%iλ %s" id (aux Down x) in
      (match pos with
       | Down -> step
       | Left | Right -> parens step)
    | App (x, y) ->
      let step = Printf.sprintf "%s %i@ %s" (aux Left x) id (aux Right y) in
      (match pos with
       | Down | Left -> step
       | Right -> parens step)
    | Var i -> Printf.sprintf "[%i]%i" id i
  in aux Down t

open Fix.Minimize
open Fix.Enum
open Fix.Indexing

module Label = struct
  type t = extpos
  let compare = compare
  let print = pr_extpos
end

let minimize (t : pure_term) : term =
  let idx, trs = calc_transition_system t in
  let size = idx + 1 in

  let module A = struct

    (* Number of states. *)
    module N = Const(struct let cardinal = size end)
    type states = N.n
    let states = N.n
    type state = states index
    let state (i : int) : state = Index.of_int states i

    let trs = Array.of_list @@ List.map (fun (s, l, t) -> state s, l, state t) trs

    (* Number of transitions. *)
    module M = Const(struct let cardinal = Array.length trs end)
    type transitions = M.n
    let transitions = M.n
    type transition = transitions index

    (* Description of transitions. *)
    let source (t : transition) =
      let s, _, _ = trs.((t :> int)) in s
    let target (t : transition) =
      let _, _, t = trs.((t :> int)) in t
    let label  (t : transition) =
      let _, l, _ = trs.((t :> int)) in l

    (* Initial and final states. *)
    let initials = singleton (state 0)
    let finals = list @@ List.init size state

    (* Extra parameters. *)
    let debug = false
    let groups = empty

  end in

  let module A' = Minimize(Label)(A) in

  let rec assign_id curr t : int * term =
    let id = (Option.get @@ A'.transport_state (A.state curr) :> int) in
    let next, term =
      match t with
      | Lam t ->
        let next, t = assign_id (curr + 1) t in
        next, Lam t
      | Var i ->
        curr, Var i
      | App (t, u) ->
        let next, t = assign_id (curr + 1) t in
        let next, u = assign_id (next + 1) u in
        next, App (t, u) in
    next, { id; term }
  in snd @@ assign_id 0 t
