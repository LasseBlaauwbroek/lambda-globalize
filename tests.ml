open Lambdahash

(** Some tests and benchmarks for the globalization algorithm. It consists
    mainly of some examples from the paper. *)
module Tests(A : sig
    include AbstractLambda
    val globalize : term -> term
  end) = struct
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

  let test t p1 p2 = hash (index p1 t) = hash (index p2 t)

  let%test "simple test" =
    let t = from_pure @@ Lam (App (Lam (Var 1), Var 0)) in
    let p1, p2 = [Down; Left; Down], [Down; Right] in
    info t [p1; p2];
    test (globalize t) p1 p2 && not @@ test t p1 p2

  let%test "example 1" =
    let t = from_pure @@ Lam (App (
        App (Lam (Var 0), (Lam (Lam (App (Var 0, Var 2))))),
        (Lam (App (Var 0, Var 1))))) in
    let p1, p2 = [Down; Left; Right; Down], [Down; Right] in
    info t [p1; p2];
    test (globalize t) p1 p2 && not @@ test t p1 p2

  let%test "example 2" =
    let t = from_pure @@ Lam (App (
        App (Lam (Var 0), (Lam (Lam (App (Var 0, Var 1))))),
        (Lam (App (Var 0, Var 1))))) in
    let p1, p2 = [Down; Left; Right; Down], [Down; Right] in
    info t [p1; p2];
    test t p1 p2 && not @@ test (globalize t) p1 p2

  let%test "example 3" =
    let t = from_pure @@ Lam (App (
        Lam (     App (     App (Var 0, Var 1),
                       Lam (App (Var 1, Var 2)))),
        Lam (Lam (App (     App (Var 0, Var 2),
                       Lam (App (Var 1, Var 3)))))
      )) in
    let p1, p2, p3, p4 = [Down; Left; Down; Left],
                         [Down; Left; Down; Right; Down],
                         [Down; Right; Down; Down; Left],
                         [Down; Right; Down; Down; Right; Down] in
    info t [p1; p2; p3; p4];
    let g = globalize t in
    test g p1 p2 && test g p2 p3 && test g p3 p4

  let%test_unit "benchmark linear term" =
    let mk_linear_term n =
      let apps = List.fold_right (fun i t -> App (t, Var i)) (List.init (n - 1) (fun i -> i)) (Var (n - 1)) in
      List.init n (fun _ -> ()) |> List.fold_left (fun t () -> Lam t) apps in
    let bench n =
      let t = from_pure @@ mk_linear_term n in
      let start = Unix.gettimeofday () in
      let _ = globalize t in
      Unix.gettimeofday () -. start in
    print_endline ("Benchmark linear terms: " ^ pr_term (from_pure @@ mk_linear_term 10));
    let timings = List.map bench @@ List.init 10 (fun i -> (i + 1) * 200) in
    print_endline ("Timings: " ^ pr_list (List.map (Printf.sprintf "%f") timings));
end

module LambdaGTerm  = LambdaImplementation(GTerm)
module LambdaDigest = LambdaImplementation(GDigest)

let%test_module _ = (module struct
  let _ = print_endline "\n\nTesting Naive with GTerms\n"
  let%test_module _ = (module Tests(NaiveGlobalize(LambdaGTerm)))

  let _ = print_endline "\n\nTesting EfficientGlobalize1 with GTerms\n"
  let%test_module _ = (module Tests(EfficientGlobalize1(LambdaGTerm)))

  let _ = print_endline "\n\nTesting EfficientGlobalize2 with GTerms\n"
  let%test_module _ = (module Tests(EfficientGlobalize2(LambdaGTerm)))

  let _ = print_endline "\n\nTesting Naive with Digests\n"
  let%test_module _ = (module Tests(NaiveGlobalize((LambdaDigest))))

  let _ = print_endline "\n\nTesting EfficientGlobalize1 with Digests\n"
  let%test_module _ = (module Tests(EfficientGlobalize1(LambdaDigest)))

  let _ = print_endline "\n\nTesting EfficientGlobalize2 with Digests\n"
  let%test_module _ = (module Tests(EfficientGlobalize2(LambdaDigest)))

end)
