(** A simple priority queue adapted from
    https://v2.ocaml.org/releases/4.01/htmlman/moduleexamples.html *)

module PrioQueue =
struct
  type priority = int
  type 'a queue = Empty | Node of priority * 'a * 'a queue * 'a queue
  let empty = Empty

  let rec insert queue prio elt =
    match queue with
    | Empty -> Node(prio, elt, Empty, Empty)
    | Node(p, e, left, right) ->
      if prio >= p
      then Node(prio, elt, insert right p e, left)
      else Node(p, e, insert right prio elt, left)

  let singleton prio elt = Node (prio, elt, Empty, Empty)

  exception Queue_is_empty
  let rec remove_top = function
    | Empty -> raise Queue_is_empty
    | Node(_, _, left, Empty) -> left
    | Node(_, _, Empty, right) -> right
    | Node(_, _, (Node(lprio, lelt, _, _) as left),
           (Node(rprio, relt, _, _) as right)) ->
      if lprio >= rprio
      then Node(lprio, lelt, remove_top left, right)
      else Node(rprio, relt, left, remove_top right)

  let pop = function
    | Empty -> None
    | Node(prio, elt, _, _) as queue -> Some (prio, elt, remove_top queue)

  let pop_multiple queue =
    Fun.flip Option.map (pop queue) @@ fun (prio, _, _) ->
    let rec aux acc queue =
      match pop queue with
      | Some (prio', t, queue) when prio = prio' ->
        aux (t::acc) queue
      | _ -> prio, acc, queue in
    aux [] queue

  let%test_module _ = (module struct
    let discard trp =
      let (s, v, _) = Option.get trp in s, v

    let%test _ = pop empty = None
    let%test _ = pop_multiple empty = None

    let q1 = singleton 2 "a"
    let%test _ = pop q1 |> discard = (2, "a")
    let%test _ = pop_multiple q1 |> discard = (2, ["a"])

    let q2 = insert q1 3 "b"
    let%test _ = pop q2 |> discard = (3, "b")
    let%test _ = pop_multiple q2 |> discard = (3, ["b"])
    let%test _ = remove_top q2 |> pop |> discard = (2, "a")

    let q2 = insert q1 1 "b"
    let%test _ = pop q2 |> discard = (2, "a")
    let%test _ = remove_top q2 |> pop |> discard = (1, "b")

    let q3 = insert q2 2 "c"
    let%test _ = pop_multiple q3 |> discard = (2, ["a"; "c"])

    let q3 = insert q2 1 "c"
    let%test _ = pop_multiple q3 |> discard = (2, ["a"])

    let q3 = insert (insert q1 3 "b") 3 "c"
    let%test _ = pop_multiple q3 |> discard = (3, ["b"; "c"])

  end)
end

module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)
