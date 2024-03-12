(** Definitions of basic terms, indexing and pretty printing *)

module IntMap = Map.Make(Int)

type 'a termf = Lam  of 'a
              | Var  of int
              | App  of 'a * 'a [@@deriving map, fold, eq]
type pure_term = pure_term termf

type pos = Down | Left | Right

let pr_termf pos pr =
  let parens t = "(" ^ t ^ ")" in
  function
  | Lam x ->
    let step = "λ " ^ pr Down x in
    (match pos with
     | Down -> step
     | Left | Right -> parens step)
  | App (x, y) ->
    let step = pr Left x ^ " " ^ pr Right y in
    (match pos with
     | Down | Left -> step
     | Right -> parens step)
  | Var i -> string_of_int i

type 'a debruijn_map =
  { map  : 'a IntMap.t
  ; size : int }
let empty_debruijn = { map = IntMap.empty; size = 0 }
let push_debruijn { map; size } t =
  { map = IntMap.add size t map
  ; size = size + 1 }
let find_debruijn { map; size } i = IntMap.find_opt (size - i - 1) map
