open Lambda_hash.Generate
open Lambda_hash.Lambdahash

module LambdaGTerm  = LambdaImplementation(LambdaSizeModifier(GTerm))

let eff_file = ref ""
let naive_file = ref ""
let size = ref 8
let amount = 1000

let _ =
  let speclist =
    [ "-s", Arg.Set_int size, "max size"
    ; "-o1", Arg.Set_string eff_file, "efficient globalize file"
    ; "-o2", Arg.Set_string naive_file, "naive globalize file"] in
  Arg.parse speclist (fun _ -> ()) "cmd -size n"

let bench from_pure globalize out =
  let out =
    if out == "" then stdout else open_out out in
  let terms = List.init !size @@ fun n -> from_pure @@ linear_term (linear_size n) in
  Printf.fprintf out "x\tmin\tq1\tq2\tq3\tmax\n";
  List.iteri (fun i t ->
        Printf.fprintf out "%i" (linear_size i * 3 - 1);
      let ls = List.init amount @@ fun _ -> (time @@ fun () -> globalize t) in
      let min, q1, q2, q3, max = stats ls in
      Printf.fprintf out "\t%.10f\t%.10f\t%.10f\t%.10f\t%.10f\n" min q1 q2 q3 max
    ) @@ terms

module G1 = EfficientGlobalize1(LambdaGTerm)
let () = bench G1.from_pure G1.globalize !eff_file
module G2 = NaiveGlobalize(LambdaGTerm)
let () = bench G2.from_pure G2.globalize !naive_file
