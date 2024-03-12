open Lambda_hash.Lambdacount
open Lambda_hash.Generate
open Lambda_hash.Lambda

let rec pr_term t =
  let rec aux parens t = pr_termf parens aux t in
  aux Down t

let () =
  let amount = 1000 in
  let size = ref 8 in
  let file = ref "" in
  let speclist =
    [ "-size", Arg.Set_int size, "max size to generate"
    ; "-o", Arg.Set_string file, "output file"] in
  Arg.parse speclist (fun _ -> ()) "cmd -size n";
  if !file = "" then
    failwith "no output file specified";

  let pool = Domainslib.Task.setup_pool ~num_domains:(Domain.recommended_domain_count () - 1) () in
  let terms = Domainslib.Task.run pool @@ (fun () ->

      let t = dynamic_lambdacount_f pool (Int.shift_left 1 !size + 1) in

      let bar ~total =
        let open Progress.Line in
        list [ spinner (); bar ~style:`UTF8 total; count_to total ] in
      Progress.with_reporter (bar ~total:!size) @@ fun f ->
      List.init !size @@ fun n ->
      f 1;
      Domainslib.Task.parallel_for_reduce ~start:0 ~finish:amount ~body:(fun _ ->
               let rstate = Gmp_random.init_default () in
               Gmp_random.seed_ui rstate (Random.bits ());
               [random_term rstate t (Int.shift_left 2 n) 0]
             ) pool List.append []) in
  let out = open_out_bin !file in
  Marshal.to_channel out terms [];
  close_out out
