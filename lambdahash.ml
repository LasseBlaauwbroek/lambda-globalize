open Lambda

module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)

(** Abstract specifications for hashes and decorated lambda terms *)

module type AbstractHash = sig
type hash
val pr_hash   : hash -> string
val eq_hash   : hash -> hash -> bool

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
    [not gclosed t -> size t < size (lift (Lam t))]
    [(if gclosed t then 0 else size t) + (if gclosed u then 0 else size u) < size (lift (App (t, u)))]

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
type hashes = hash debruijn_map
let empty_hashes = empty_debruijn
let push_hash = push_debruijn
let find_subst = find_debruijn
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

module Heap (L : AbstractLambda) = struct
  open L

  include Containers.Heap.Make(struct type t = term let leq t1 t2 = size t1 >= size t2 end)

  let pop_multiple queue =
    Fun.flip Option.map (find_min queue) @@ fun t ->
    let prio = L.size t in
    let rec aux acc queue =
      match take queue with
      | Some (queue, t) when prio = L.size t ->
        aux (t::acc) queue
      | _ -> prio, acc, queue in
    aux [] queue
end

(** An efficient O(n log n) globalization algorithm. *)
module EfficientGlobalize1 (L : AbstractLambda) = struct
include L include BasicOperations(L)
module Heap = Heap(L)

let calc_duplicates (t : term) : IntSet.t =
  let step q t = if gclosed t then q else Heap.insert t q in
  let rec aux queue =
    match Heap.pop_multiple queue with
    | None -> IntSet.empty
    | Some (_,  [t], queue) -> aux (fold_termf step queue (case t))
    | Some (size, _, queue) -> IntSet.add size (aux queue)
  in aux (Heap.insert t Heap.empty)

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
module Heap = Heap(L)

(** [fill_lambda t queue] will insert all subterms of [t] in the [queue] that
    are lambdas, and do not have a lambda as a parent. *)
let rec fill_lambda t queue =
  let step queue t = if gclosed t then queue else match case t with
      | Lam _ -> Heap.insert t queue
      | _ -> fill_lambda t queue in
  fold_termf step queue (case t)

let calc_duplicates (t : term) : IntSet.t =
  let rec aux queue =
    match Heap.pop_multiple queue with
    | None -> IntSet.empty
    | Some (size,  [t], queue) -> aux (fill_lambda t queue)
    | Some (size, _, queue) -> IntSet.add size (aux queue)
  in aux (fill_lambda t Heap.empty)

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

type ('a, 'b) gtermf = Term of 'a | GVar of 'b [@@deriving map, eq]

(** An implementation of the hash structure as g-terms. *)
module GTerm: AbstractHash = struct
type hash = (hash termf, hash) gtermf
let lift_hash h = Term h
let hash_gvar h = GVar h

let eq_hash = (=)
let pr_hash t =
  let rec aux parens = function
    | GVar h -> "g(" ^ aux Down h ^ ")"
    | Term t -> pr_termf parens aux t in
  aux Down t
end

(** An implementation of the hash structure as a digest that is more efficient
    to compare than g-terms. *)
module GDigest: AbstractHash with type hash = string = struct
type hash = string
let lift_hash h = Digest.string (pr_termf Right (fun _ h -> h) h)
let hash_gvar h = Digest.string ("g(" ^ h ^ ")")
let eq_hash = (=)
let pr_hash t = t
end

module GInt: AbstractHash with type hash = int = struct
type hash = int
let lift_hash h =
  Hashtbl.hash (Term h)
let hash_gvar h = Hashtbl.hash (GVar h)
let eq_hash = (=)
let pr_hash t = string_of_int t
end

(** An implementation of the hash structure as g-terms with perfect sharing
    obtained through the hashcons library. With this implementation, g-terms can
    be compared in constant time using (==), without the risk of collisions. In
    a sense, this is the best of both worlds between the previous two
    implementations. Benchmarks show that the overhead of hash-consing is
    significant though. Use with caution. *)

type hashcons_gterm = (hashcons_gterm termf, hashcons_gterm) gtermf Hashcons.hash_consed
module GTermConsed: AbstractHash with type hash = hashcons_gterm = struct
  open Hashcons

  type hash = hashcons_gterm

  module H = Make(struct
    type t = (hash termf, hash) gtermf
    let equal = equal_gtermf (equal_termf (==)) (==)
    let hash t =
      let h t = t.hkey in
      Hashtbl.hash (map_gtermf (map_termf h) h t)
  end)

  let ht = H.create 10000000
  let lift_hash h = H.hashcons ht (Term h)
  let hash_gvar h = H.hashcons ht (GVar h)

  let eq_hash = (==)
  let pr_hash h =
    let rec aux parens { node; _ } =
      match node with
      | GVar h -> "g(" ^ aux Down h ^ ")"
      | Term t -> pr_termf parens aux t in
    aux Down h
end

type 'a decorated_hash =
  { hash : 'a
  ; size : int
  ; free : int }

let decorated_hash { hash; _ } = hash
let decorate_size { size; _ }  = size
let decorated_closed { free; _ } = free < 0


module type HashWithSizeModifier = sig
  include AbstractHash
  val modify_size : hash decorated_hash -> int
  val gvar_size   : hash decorated_hash -> int
end

module ClosedZeroSizeModifier(H : AbstractHash) :
  HashWithSizeModifier with type hash = H.hash = struct
  include H
  let modify_size h = if decorated_closed h then 0 else decorate_size h
  let gvar_size _ = 0
end
module LambdaSizeModifier(H : AbstractHash) :
  HashWithSizeModifier with type hash = H.hash = struct
  include H
  let modify_size = decorate_size
  let gvar_size _ = 0
end
module GTermSizeModifier(H : AbstractHash) :
  HashWithSizeModifier with type hash = H.hash = struct
  include H
  let modify_size = decorate_size
  let gvar_size = modify_size
end
module IntHashSizeModifier(H : AbstractHash with type hash = int) :
  HashWithSizeModifier with type hash = H.hash = struct
  include H
  let modify_size h =
    if decorated_closed h then
      (* Truncate the hash to 32 bits *)
      Int.logand (decorated_hash h) 4294967295
    else
      decorate_size h
  let gvar_size = modify_size
end
module IntHashConsSizeModifier(H : AbstractHash with type hash = hashcons_gterm) :
  HashWithSizeModifier with type hash = H.hash = struct
  include H
  let modify_size h =
    if decorated_closed h then
      (* Truncate the hash to 32 bits *)
      Int.logand Hashcons.((decorated_hash h).hkey) 4294967295
    else
      decorate_size h
  let gvar_size = modify_size
end
module StringHashSizeModifier(H : AbstractHash with type hash = string) :
  HashWithSizeModifier with type hash = H.hash = struct
  include H
  let modify_size h =
    if decorated_closed h then
      (* Truncate the hash to 32 bits *)
      Int32.to_int (String.get_int32_ne (decorated_hash h) 0)
    else
      decorate_size h
  let gvar_size = modify_size
end

(** The actual implementation of decorated lambda terms. *)
module LambdaImplementation(H : HashWithSizeModifier): AbstractLambda with type hash = H.hash decorated_hash = struct

type hash = H.hash decorated_hash

let pr_hash { hash; _ } = H.pr_hash hash
let eq_hash h1 h2 = H.eq_hash h1.hash h2.hash
let lift_hash ht =
  { hash = H.lift_hash (map_termf decorated_hash ht)
  ; free = (match ht with
        | Var i -> i
        | Lam { free; _ } -> free - 1
        | _     -> fold_termf (fun m { free; _ } -> max m free) (-1) ht)
  ; size = fold_termf (fun m h -> m + H.modify_size h) 1 ht }
let hash_gvar h = { hash = H.hash_gvar (decorated_hash h); size = 1 + H.gvar_size h; free = -1 }

type term = { term : term termf
            ; hash : hash }

let hash { hash; _ } = hash
let size { hash; _ } = decorate_size hash
let lift term =
  { term
  ; hash = lift_hash (map_termf hash term) }
let case { term; _ } = term
let gvar h i = { term = Var i; hash = hash_gvar h }
let gclosed { hash; _ } = decorated_closed hash

end
