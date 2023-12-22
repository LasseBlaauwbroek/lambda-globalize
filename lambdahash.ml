open Helpers

(** Definitions of basic terms, indexing and pretty printing *)

type 'a termf = Lam  of 'a
              | Var  of int
              | App  of 'a * 'a [@@deriving map, fold]
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

(** Abstract specifications for hashes and decorated lambda terms *)

module type AbstractHash = sig
type hash
val pr_hash   : hash -> string
val lift_hash : hash termf -> hash
val hash_gvar : hash -> hash
end

module type AbstractLambda = sig
include AbstractHash

type term
val lift : term termf -> term
val case : term -> term termf
(** Contract:
    [case (lift t) = t]
*)

val hash    : term -> hash
(** Contract:
    [hash (lift t) = lift_hash (map_termf hash) t]
*)

val gvar    : hash -> int -> term
(** Contract:
    [case (gvar h i) = Var i]
    [hash (gvar h i) = hash_gvar h]
*)

val gclosed : term -> bool
(** Contract:
    [gclosed t = free t < 0]
    [free (gvar h i) = -1]
    [free (lift (Var i)) = i]
    [free (lift (Lam t)) = free t - 1]
    [free (lift (App (t, u))) = max (free t) (free u)]
*)

val size : term -> int
(** Contract:
    [size t < size (lift (Lam t))]
    [size t + size u < size (lift (App (t, u)))]

    Additionally, we must have that if two term nodes are context-sensitive
    alpha-equivalent, they have the same size.
*)

end

(** Basic operations on lambda terms and hashes *)

module BasicOperations(L : AbstractLambda) : sig
open L

val pr_term : term -> string

(** Conversion between pure terms and decorated terms *)
val from_pure : pure_term -> term
val to_pure   : term -> pure_term

(** [set_hash i h t] decorates de Bruijn indices i with hash h in t. *)
val set_hash : int -> hash -> term -> term

(** Set multiple hashes at the same time. *)
type hashes
val empty_hashes : hashes
val push_hash    : hashes -> hash -> hashes
val set_hashes   : hashes -> term -> term
(** Contract:
    [set_hashes (List.fold_left push_hash empty_hashes ls) t =
     List.fold_left (|>) t (List.mapi set_hash ls)]
*)

end = struct
open L

let pr_term (t : term) =
  let rec aux parens t =
    pr_termf parens aux (case t) in
  aux Down t

(** Example of converting a term to a pure_term and back *)
let rec from_pure (t : pure_term) : term = lift (map_termf from_pure t)
let rec to_pure   (t : term) : pure_term = map_termf to_pure (case t)

let rec set_hash (n : int) (h : hash) (t : term) : term =
  if gclosed t then t (* do not modify existing g-vars *)
  else match case t with
    | Lam t -> lift (Lam (set_hash (n+1) h t))
    | Var i -> if n = i then gvar h i else t
    | t     -> lift (map_termf (set_hash n h) t)

(** We cannot implement hashes as a list. That would be too slow. Instead, we
    implement it using a map. *)
type hashes =
  { map  : hash IntMap.t
  ; size : int }
let empty_hashes = { map = IntMap.empty; size = 0 }
let push_hash { map; size } t =
  { map = IntMap.add size t map
  ; size = size + 1 }
let find_subst { map; size } i = IntMap.find_opt (size - i - 1) map
let rec set_hashes (s : hashes) (t : term) : term =
  if gclosed t then t else
    match case t with
    | Lam t -> lift @@ Lam (set_hashes { s with size = s.size + 1 } t)
    | Var i -> Option.fold ~none:t ~some:(fun h -> gvar h i) (find_subst s i)
    | t -> lift @@ map_termf (set_hashes s) t

end

(** A simple, naive O(n^2) globalization algorithm. *)
module NaiveGlobalize (L : AbstractLambda) = struct
include L include BasicOperations(L)

let rec globalize (t : term) : term =
  match case t with
  | Lam t' -> lift (Lam (globalize (set_hash 0 (hash t) t')))
  | Var _  -> t
  | t      -> lift (map_termf globalize t)

end

(** An efficient O(n log n) globalization algorithm. *)
module EfficientGlobalize1 (L : AbstractLambda) = struct
include L include BasicOperations(L)

let calc_duplicates (t : term) : IntSet.t =
  let step q t = if gclosed t then q else PrioQueue.insert q (size t) t in
  let rec aux queue =
    match PrioQueue.pop_multiple queue with
    | None -> IntSet.empty
    | Some (_,  [t], queue) -> aux (fold_termf step queue (case t))
    | Some (size, _, queue) -> IntSet.add size (aux queue)
  in aux (PrioQueue.singleton (size t) t)

let rec globalize (r : term) : term =
  let duplicates = calc_duplicates r in
  let rec globalize_scc (s : hashes) (t : term) =
    match case t with
    | Lam t' ->
      let s = push_hash s (hash (lift (App (r, t)))) in
      lift (Lam (globalize_step s t'))
    | Var _ -> set_hashes s t
    | t -> lift (map_termf (globalize_step s) t)
  and globalize_step s t =
    let t = if IntSet.mem (size t) duplicates then set_hashes s t else t in
    if gclosed t then globalize t else globalize_scc s t
  in globalize_scc empty_hashes r

end

(** An even more efficient globalization algorithm. The additional optimization
    here is that we only perform substitutions when we encounter a lambda.
    Similarly, we do not need to consider application nodes when calculating the
    set of duplicate nodes.

    This optimization does not lead to an asymptotic speed improvement, but may
    still be good in practice.
*)
module EfficientGlobalize2 (L : AbstractLambda) = struct
include L include BasicOperations(L)

(** [fill_lambda t queue] will insert all subterms of [t] in the [queue] that
    are lambdas, and do not have a lambda as a parent. *)
let rec fill_lambda t queue =
  let step queue t = if gclosed t then queue else match case t with
      | Lam _ -> PrioQueue.insert queue (size t) t
      | _ -> fill_lambda t queue in
  fold_termf step queue (case t)

let calc_duplicates (t : term) : IntSet.t =
  let rec aux queue =
    match PrioQueue.pop_multiple queue with
    | None -> IntSet.empty
    | Some (size,  [t], queue) -> aux (fill_lambda t queue)
    | Some (size, _, queue) -> IntSet.add size (aux queue)
  in aux (fill_lambda t PrioQueue.empty)

let rec globalize (r : term) : term =
  let duplicates = calc_duplicates r in
  let rec globalize_scc (s : hashes) (t : term) =
    match case t with
    | Lam t' ->
      let s = push_hash s (hash (lift (App (r, t)))) in
      lift (Lam (globalize_step s t'))
    | Var _ -> set_hashes s t
    | t -> lift (map_termf (globalize_step s) t)
  and globalize_step s t =
    let t = match case t with
      | Lam _ when IntSet.mem (size t) duplicates -> set_hashes s t
      | _ -> t in
    if gclosed t then globalize t else globalize_scc s t
 in globalize_scc empty_hashes r

end

(** An implementation of the hash structure as g-terms. *)
module GTerm: AbstractHash = struct
type hash = Term of hash termf | GVar of hash
let lift_hash h = Term h
let hash_gvar h = GVar h

let pr_hash t =
  let rec aux parens = function
    | GVar h -> "g(" ^ aux Down h ^ ")"
    | Term t -> pr_termf parens aux t in
  aux Down t
end

(** An implementation of the hash structure as a digest that is more efficient
    to compare than g-terms. *)
module GDigest: AbstractHash = struct
type hash = string
let lift_hash h = Digest.string (pr_termf Right (fun _ h -> h) h)
let hash_gvar h = Digest.string ("g(" ^ h ^ ")")
let pr_hash t = t
end

(** The actual implementation of decorated lambda terms. *)
module LambdaImplementation(H: AbstractHash): AbstractLambda = struct
include H

(** Every node caches the hash of the term, the size, and how what the largest
    free variable in the term is. *)
type term = { term : term termf
            ; hash : hash
            ; size : int
            ; free : int }

let hash { hash; _ } = hash
let size { size; _ } = size
let lift term =
  let free = match term with
    | Var i -> i
    | _     -> fold_termf (fun m { free; _ } -> max m free) (-1) term in
  let size = fold_termf (fun m { size; _ } -> m + size) 1 term in
  { term; size; free
  ; hash = lift_hash (map_termf hash term) }
let case { term; _ } = term
let gvar h i = { term = Var i; hash = hash_gvar h; size = 1; free = -1 }
let gclosed { free; _ } = free < 0

end

