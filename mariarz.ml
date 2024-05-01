module IntMap = Lambda.IntMap

let gen_var =
  let v = ref 0 in
  fun () ->
    let res = !v in
    v := !v + 1;
    res

type 'a termf =
  | Var of int
  | Lam of int * 'a
  | App of 'a * 'a [@@deriving map, fold]

type pure_term = pure_term termf

type pos = Down | Left | Right

let pr_termf pos pr =
  let parens t = "(" ^ t ^ ")" in
  function
  | Lam (x, y) ->
    let step = "λ" ^ string_of_int x ^ ". " ^ pr Down y in
    (match pos with
     | Down -> step
     | Left | Right -> parens step)
  | App (x, y) ->
    let step = pr Left x ^ " " ^ pr Right y in
    (match pos with
     | Down | Left -> step
     | Right -> parens step)
  | Var i -> string_of_int i

let rec pr_term t =
  let rec aux parens t = pr_termf parens aux t in aux Down t

type 'a postreef =
  | Here
  | Join of int * 'a option * 'a

type ('a, 'b) structuref =
  | Var
  | Lam of 'b option * 'a
  | App of bool * 'a * 'a [@@deriving map, fold]

module type HashStructure = sig

  type postree
  type structure
  type var_map

  val lift_postree : postree postreef -> postree
  val lift_structure : (structure, postree) structuref -> structure

  val structure_tag : structure -> int

  val map_update : var_map -> int -> (postree option -> postree option) -> var_map
  val map_empty : var_map
  val map_bindings : var_map -> (int * postree) list
  val map_size : var_map -> int
  val map_find : var_map -> int -> postree option

  val eq_map : var_map -> var_map -> bool
  val eq_structure : structure -> structure -> bool
end

module type InvertibleHashStructure = sig
  include HashStructure
  val case_postree : postree -> postree postreef
  val case_structure : structure -> (structure, postree) structuref
end

module InvertibleHash : InvertibleHashStructure = struct
  type postree = postree postreef
  type structure = { tag : int; s : (structure, postree) structuref }
  type var_map =
    { map : postree IntMap.t
    ; size : int }

  let lift_postree x = x
  let structure_tag { tag ; _ } = tag
  let lift_structure s =
    { s; tag = fold_structuref (fun d s -> 1 + Int.max d (structure_tag s)) (fun x _ -> x) 0 s}

  let case_postree p = p
  let case_structure { s; _ } = s

  let map_update { map; size } x f =
    let v = IntMap.find_opt x map in
    let v' = f v in
    let map = IntMap.update x (fun _ -> v') map in
    let size = match v, v' with
      | None, None -> size
      | None, Some _ -> size + 1
      | Some _, None -> size - 1
      | Some _, Some _ -> size in
    { map; size }

  let map_empty = { map = IntMap.empty; size = 0 }
  let map_bindings { map; _ } = IntMap.bindings map
  let map_size { size; _ } = size
  let map_find { map; _ } x = IntMap.find_opt x map

  let eq_map m1 m2 = IntMap.equal (=) m1.map m2.map
  let eq_structure = (=)

end

module IntHash : HashStructure = struct
  type postree = int
  type structure = { tag : int; s : int }
  type var_map =
    { map : postree IntMap.t
    ; size : int
    ; hash : int }

  let lift_postree x = Hashtbl.hash x
  let structure_tag { tag ; _ } = tag
  let lift_structure s =
    { s = Hashtbl.hash @@ map_structuref (fun { s; _ } -> s) (fun x -> x) s
    ; tag = fold_structuref (fun d s -> 1 + Int.max d (structure_tag s)) (fun x _ -> x) 0 s}

  let entry_hash x v = Hashtbl.hash (x, v)
  let xor = Int.logxor
  let map_update { map; size; hash } x f =
    let v = IntMap.find_opt x map in
    let v' = f v in
    let map = IntMap.update x (fun _ -> v') map in
    let size, hash = match v, v' with
      | None, None -> size, hash
      | None, Some p -> size + 1, xor hash (entry_hash x p)
      | Some p, None -> size - 1, xor hash (entry_hash x p)
      | Some p1, Some p2 -> size, xor (xor hash (entry_hash x p1)) (entry_hash x p2)
    in { map; size; hash }

  let map_empty = { map = IntMap.empty; size = 0; hash = Hashtbl.hash () }
  let map_bindings { map; _ } = IntMap.bindings map
  let map_size { size; _ } = size
  let map_find { map; _ } x = IntMap.find_opt x map

  let eq_map m1 m2 = m1.hash = m2.hash
  let eq_structure = (=)

end

module Algorithm(H : HashStructure) = struct
  open H

  type esummary = structure * var_map

  type hashed_term = { term : hashed_term termf; hash : esummary }
  let hash { hash; _ } = hash

  let lift_summary : esummary termf -> esummary = function
    | Var x -> lift_structure Var, map_update map_empty x (fun _ -> Some (lift_postree Here))
    | Lam (x, (t, m)) ->
      let pos = map_find m x in
      let m = map_update m x (fun _ -> None) in
      lift_structure (Lam (pos, t)), m
    | App ((t, l), (u, r)) ->
      let left_bigger = map_size l > map_size r in
      let tu = lift_structure (App (left_bigger, t, u)) in
      let tag = structure_tag tu in
      let bigm, smallm = if left_bigger then l, r else r, l in
      let add m (x, pos) =
        map_update m x (fun mpos -> Some (lift_postree (Join (tag, mpos, pos)))) in
      let m = List.fold_left add bigm (map_bindings smallm) in
      tu, m

  let rec summarize (t : pure_term) : hashed_term =
    let term = map_termf summarize t in
    { term; hash = lift_summary (map_termf hash term) }
end

module ReverseAlgorithm(H : InvertibleHashStructure) = struct
  open H
  let find_singleton map =
    match map_bindings map with
    | [ x, _ ] -> x
    | _ -> assert false

  let filter_map map f =
    List.fold_left (fun m (x, v) ->
        map_update m x (fun _ -> f v)) map_empty (map_bindings map)

  type esummary = structure * var_map

  let rec rebuild ((t, m) : esummary) : pure_term =
    match case_structure t with
    | Var -> Var (find_singleton m)
    | Lam (p, t) ->
      let x = gen_var () in
      Lam (x, rebuild (t, map_update m x (fun _ -> p)))
    | App (left_bigger, tl, tr) ->
      let tag = structure_tag t in
      let upd_small s =
        match case_postree s with
        | Join (ptag, mp, p) when ptag = tag -> Some p
        | _ -> None in
      let update_big s =
        match case_postree s with
        | Join (ptag, mp, p) when ptag = tag -> mp
        | _ -> Some s in
      let small_m = filter_map m upd_small in
      let big_m = filter_map m update_big in
      let ml, mr = if left_bigger then (big_m, small_m) else (small_m, big_m) in
      App (rebuild (tl, ml), rebuild (tr, mr))
end

let%test "test summarize -> rebuild" =
  let open Algorithm(InvertibleHash) in
  let open ReverseAlgorithm(InvertibleHash) in
  let t : pure_term = Lam (0, (Var 0)) in
  print_endline (pr_term t);
  let t' = rebuild @@ hash @@ summarize t in
  print_endline (pr_term t');
  t' = t

let debruijn2term (t : Lambda.pure_term) : pure_term =
  let module B = Lambda in
  let rec aux map : B.pure_term -> pure_term = function
    | B.Var i -> Var (Option.get @@ B.find_debruijn map i)
    | B.Lam t ->
      let x = gen_var () in
      Lam (x, aux (B.push_debruijn map x) t)
    | B.App (t, u) -> App (aux map t, aux map u) in
  aux B.empty_debruijn t

let alpha_equiv t1 t2 =
  let rec aux map : pure_term * pure_term -> bool = function
    | Var x1, Var x2 -> (match IntMap.find_opt x1 map with
        | Some x3 -> x2 = x3
        | None -> false)
    | Lam (x1, t1), Lam (x2, t2) -> aux (IntMap.add x1 x2 map) (t1, t2)
    | App (t1l, t1r), App (t2l, t2r) -> aux map (t1l, t2l) && aux map (t1r, t2r)
    | _, _ -> false
  in aux IntMap.empty (t1, t2)

let%test "test summarize -> rebuild" =
  let open Algorithm(InvertibleHash) in
  let open ReverseAlgorithm(InvertibleHash) in
  let t = debruijn2term @@ Generate.balanced_term 1000 in
  print_endline (pr_term t);
  let t' = rebuild @@ hash @@ summarize t in
  print_endline (pr_term t');
  alpha_equiv t t'
