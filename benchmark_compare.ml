open Lambda_hash.Generate
open Lambda_hash.Lambdahash

module LambdaGInt  = LambdaImplementation(IntHashSizeModifier(GInt))
module LambdaGTermCons  = LambdaImplementation(IntHashConsSizeModifier(GTermConsed))

let output_balanced = ref ""
let output_linear = ref ""
let size = ref 8
let amount = 30

let _ =
  let speclist =
    [ "-s", Arg.Set_int size, "max size"
    ; "-o1", Arg.Set_string output_balanced, "output file balanced"
    ; "-o2", Arg.Set_string output_linear, "output file linear"] in
  Arg.parse speclist (fun _ -> ()) "cmd -size n"

let bench from_pure globalize =
  let balanced = List.init (!size - 1) @@ fun n -> List.init amount @@ fun _ -> from_pure @@ balanced_term (balanced_size n) in
  let b1 = List.map (fun ls ->
      let ls = List.map (fun t -> time @@ fun () -> globalize t) ls in
      let min, q1, q2, q3, max = stats ls in
      q2
    ) @@ balanced in
  let linear = List.init !size @@ fun n -> List.init amount @@ fun _ -> from_pure @@ linear_term (linear_size n) in
  let b2 = List.map (fun ls ->
      let ls = List.map (fun t -> time @@ fun () -> globalize t) ls in
      let min, q1, q2, q3, max = stats ls in
      q2
    ) @@ linear in
  b1, b2

module G1 = EfficientGlobalize2(LambdaGInt)
module G2 = EfficientGlobalize2(LambdaGTermCons)
module Valmari = Lambda_hash.Valmari
module Mariarz = Lambda_hash.Mariarz
module MariarzAlg = Mariarz.Algorithm(Mariarz.IntHash)

let () =
  let runs =
    [ "oursint", bench G1.from_pure G1.globalize
    ; "ourscons", bench G2.from_pure G2.globalize
    ; "valmari", bench (fun x -> x) Valmari.minimize
    ; "mariarz", bench Mariarz.debruijn2term MariarzAlg.summarize
    ] in

  let write_file out x_size select =
    let headers = "x\t" ^ String.concat "\t" @@ List.map fst runs in
    let contents =
      String.concat "\n" @@
      List.mapi (fun i str -> Printf.sprintf "%i\t%s" (x_size i) str) @@
      List.map (String.concat "\t") @@
      List.map (List.map (Printf.sprintf "%.10f")) @@
      Lambda_hash.Tests.transpose @@ List.map select @@ List.map snd runs in
    Printf.fprintf out "%s\n%s\n" headers contents in

  let out =
    if !output_balanced == "" then stdout else open_out !output_balanced in
  write_file out balanced_size fst;
  let out =
    if !output_linear == "" then stdout else open_out !output_linear in
  write_file out (fun i -> linear_size i * 3 - 1) snd
