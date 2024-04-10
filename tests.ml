open Lambda
open Lambdahash

(** Some tests and benchmarks for the globalization algorithm. It consists
    mainly of some examples from the paper. *)

let simple_example = Lam (App (Lam (Var 1), Var 0))
let example_1 = Lam (App (
    App (Lam (Var 0), (Lam (Lam (App (Var 0, Var 2))))),
    (Lam (App (Var 0, Var 1)))))
let example_2 = Lam (App (
    App (Lam (Var 0), (Lam (Lam (App (Var 0, Var 1))))),
    (Lam (App (Var 0, Var 1)))))
let example_3 =
  Lam (App (
    Lam (     App (     App (Var 0, Var 1),
                   Lam (App (Var 1, Var 2)))),
    Lam (Lam (App (     App (Var 0, Var 2),
                   Lam (App (Var 1, Var 3)))))
  ))

let bug_1 =
  let t = Lam (App (Lam (Lam (App (Var 0, Var 1))),
                        (Lam (App (Var 0, Var 1))))) in
  App (t, t)

let all_terms = [simple_example; example_1; example_2; example_3; bug_1]

module type Globalizer = sig
  include AbstractLambda
  val globalize : term -> term
end
module HashTests(A : Globalizer) = struct
  open A
  open BasicOperations(A)

  let pr_pos = function
    | Down -> "↓"
    | Left -> "↙"
    | Right -> "↘"
  let pr_index ls = "[" ^ List.fold_left (^) "" (List.map pr_pos ls) ^ "]"
  let pr_list ls = List.fold_left (fun s p -> p ^ ", " ^ s) (List.hd ls) (List.tl ls)

  let rec index ls t = match ls, case t with
    | [], _ -> t
    | Down::ls, Lam t
    | Left::ls, App (t, _)
    | Right::ls, App (_, t) -> index ls t
    | _ -> failwith "Incorrect index"

  let info t ps =
    print_endline ("Testing: " ^ pr_term t ^ " at " ^ pr_list (List.map pr_index ps))

  let test t p1 p2 = eq_hash (hash (index p1 t)) (hash (index p2 t))

  let%test "simple test" =
    let t = from_pure simple_example in
    let p1, p2 = [Down; Left; Down], [Down; Right] in
    info t [p1; p2];
    test (globalize t) p1 p2 && not @@ test t p1 p2

  let%test "example 1" =
    let t = from_pure example_1 in
    let p1, p2 = [Down; Left; Right; Down], [Down; Right] in
    info t [p1; p2];
    test (globalize t) p1 p2 && not @@ test t p1 p2

  let%test "example 2" =
    let t = from_pure example_2 in
    let p1, p2 = [Down; Left; Right; Down], [Down; Right] in
    info t [p1; p2];
    test t p1 p2 && not @@ test (globalize t) p1 p2

  let%test "example 3" =
    let t = from_pure example_3 in
    let p1, p2, p3, p4 = [Down; Left; Down; Left],
                         [Down; Left; Down; Right; Down],
                         [Down; Right; Down; Down; Left],
                         [Down; Right; Down; Down; Right; Down] in
    info t [p1; p2; p3; p4];
    let g = globalize t in
    test g p1 p2 && test g p2 p3 && test g p3 p4

  let%test "reproducing example of a bug where 'gclosed' was implemented wrong" =
    let t = from_pure @@ bug_1 in
    let p1, p2 = [Left; Down; Left; Down; Down; Left], [Left; Down; Right; Down; Left] in
    info t [p1; p2];
    test t p1 p2 && not @@ test (globalize t) p1 p2
end

let hashers : (string * (module AbstractHash)) list =
  [ "GTerm", (module GTerm)
  ; "GDigest", (module GDigest)
  ; "GTermConsed", (module GTermConsed) ]

let hashers_with_modifiers : (string * (module HashWithSizeModifier)) list =
  List.map (fun (s, (module M : AbstractHash)) ->
      "ClosedZeroSizeModifier("^s^")", (module ClosedZeroSizeModifier(M) : HashWithSizeModifier)) hashers @
  List.map (fun (s, (module M : AbstractHash)) ->
      "LambdaSizeModifier("^s^")", (module LambdaSizeModifier(M) : HashWithSizeModifier)) hashers @
  List.map (fun (s, (module M : AbstractHash)) ->
      "GTermSizeModifier("^s^")", (module GTermSizeModifier(M) : HashWithSizeModifier)) hashers @
  [ "StringHashSizeModifier(GDigest)", (module StringHashSizeModifier(GDigest))
  ; "IntHashSizeModifier(GTermConsed)", (module IntHashConsSizeModifier(GTermConsed)) ]

module type T = sig end
module type Alg = functor (H : AbstractLambda) -> Globalizer with type hash = H.hash

let algs : (string * (module Alg)) list =
  [ "NaiveGlobalize", (module NaiveGlobalize)
  ; "EfficientGlobalize1", (module EfficientGlobalize1)
  ; "EfficientGlobalize2", (module EfficientGlobalize2) ]

let%test_module _ = (module struct

  let () =
    List.iter (fun (m, (module M : HashWithSizeModifier)) ->
        List.iter (fun (a, (module A : Alg)) ->
            Printf.printf "\n\nTesting %s(%s)\n" a m;
            ignore(module HashTests(A(LambdaImplementation(M))) : T)
          ) algs
      ) hashers_with_modifiers

end)

module type Minimizer = sig
  val minimize : pure_term -> Valmari.term
end
module Globalize2Minimize(A : Globalizer with type hash = hashcons_gterm decorated_hash) : Minimizer = struct
  open A
  open BasicOperations(A)
  let rec to_min_term t =
    Valmari.{ id = (decorated_hash @@ hash t).tag; term = map_termf to_min_term (case t) }
  let minimize t = to_min_term @@ globalize @@ from_pure t
end

(* https://stackoverflow.com/a/72282847 *)
let transpose m =
  if m = [] then [] else
    let open List in
    let empty_rows = map (fun _ -> []) (hd m) in
    fold_right (map2 cons) m empty_rows

let check_bijection ts =
  let rec flatten acc Valmari.{ id; term } =
    fold_termf flatten (id::acc) term in
  let ts = List.map (flatten []) ts in
  let ts = transpose ts in
  let check maps (ls : int list) =
    List.map2 (fun map i -> IntMap.update i (function
        | None -> Some ls
        | Some ls' -> assert (ls = ls'); Some ls') map
      ) maps ls in
  ignore(List.fold_left check (List.init (List.length (List.hd ts)) (fun _ -> IntMap.empty)) ts)

let rec pr_term t =
  let rec aux parens t = pr_termf parens aux t in aux Down t

let%test "check minimization" =
  let hashers_with_modifiers : (string * (module HashWithSizeModifier with type hash = hashcons_gterm)) list =
    [ "ClosedZeroSizeModifier(GTermConsed)", (module ClosedZeroSizeModifier(GTermConsed))
    ; "LambdaSizeModifier(GTermConsed)", (module LambdaSizeModifier(GTermConsed))
    ; "GTermSizeModifier(GTermConsed)", (module GTermSizeModifier(GTermConsed))
    ; "IntHashConsSizeModifier(GTermConsed)", (module IntHashConsSizeModifier(GTermConsed)) ] in
  let minimizers : (string * (module Minimizer)) list =
    ("Valmari", (module Valmari)) ::
    List.concat_map (fun (a, (module A : Alg)) ->
        List.map (fun (m, (module M : HashWithSizeModifier with type hash = hashcons_gterm)) ->
            Printf.sprintf "%s(%s)" a m,
            (module Globalize2Minimize(A(LambdaImplementation(M))) : Minimizer)
          ) hashers_with_modifiers
      ) algs in
  let test_term ~print t =
    Printf.printf "\n\nTesting minimization of %s\n" (pr_term t);
    let ts = List.map (fun (s, (module M : Minimizer)) -> s, M.minimize t) minimizers in
    if print then List.iter (fun (s, t) -> Printf.printf "%s\t %s\n" s (Valmari.pr_term t)) ts;
    check_bijection @@ List.map snd ts in
  List.iter (test_term ~print:true) all_terms;

  let t = Generate.balanced_term 254 in
  test_term ~print:false t;
  true
