open Lambda_hash.Generate
open Lambda_hash.Lambdahash
open Lambda_hash.Lambda

module LambdaGTerm  = LambdaImplementation(LambdaSizeModifier(GTerm))

let terms = ref ""
let eff_file = ref ""
let naive_file = ref ""
let valmari_file = ref ""

let _ =
  let speclist =
    [ "-in", Arg.Set_string terms, "pre-generated terms"
    ; "-o1", Arg.Set_string eff_file, "efficient globalize file"
    ; "-o2", Arg.Set_string naive_file, "naive globalize file"
    ; "-o3", Arg.Set_string valmari_file, "valmari minimize file"] in
Arg.parse speclist (fun _ -> ()) "cmd -size n"

let bench from_pure globalize out =
  let out =
    if out == "" then stdout else open_out out in

  let fin = open_in_bin !terms in
  let terms : pure_term list list = Marshal.from_channel fin in
  let terms = List.map (List.map from_pure) terms in

  Printf.fprintf out "x\tmin\tq1\tq2\tq3\tmax\n";
  List.iteri (fun i ls ->
      Printf.fprintf out "%i" (Int.shift_left 2 i);
      let ls = List.map (fun t -> (time @@ fun () -> globalize t)) ls in
      let min, q1, q2, q3, max = stats ls in
      Printf.fprintf out "\t%.10f\t%.10f\t%.10f\t%.10f\t%.10f\n" min q1 q2 q3 max
    ) @@ terms

module G1 = EfficientGlobalize1(LambdaGTerm)
let () = bench G1.from_pure G1.globalize !eff_file
module G2 = NaiveGlobalize(LambdaGTerm)
let () = bench G2.from_pure G2.globalize !naive_file
module V = Lambda_hash.Valmari
let () = bench (fun x -> x) V.minimize !valmari_file
