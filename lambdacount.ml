let rec naive_lambdacount n m =
  let open Z in
  match n with
  | 0 -> Z.zero
  | 1 -> ~$ m
  | _ -> naive_lambdacount Stdlib.(n - 1) Stdlib.(m + 1) +
         (List.fold_left (+) Z.zero @@ List.init Stdlib.(n - 1)
            (fun i -> naive_lambdacount i m * naive_lambdacount Stdlib.(n - 1 - i) m))

let%test "compare to oeis A135501" =
  let oeis = List.map Z.of_int [0; 0; 1; 2; 4; 13; 42; 139; 506; 1915; 7558; 31092; 132170; 580466; 2624545] in
  oeis = List.init 15 @@ fun i -> naive_lambdacount i 0

let rec naive_lambdacount_balanced n m =
  let open Z in
  match n with
    | 0 -> Z.zero
    | 1 -> ~$ m
    | _ -> if Stdlib.(n mod 2 == 0) then
        naive_lambdacount_balanced Stdlib.(n - 1) Stdlib.(m + 1)
      else naive_lambdacount_balanced Stdlib.((n - 1)/2) m ** 2

let dynamic_lambdacount s =
  let arr = Array.init s (fun i -> Array.make (s - i) Z.zero) in
  let fill (n : int) (m : int) =
    let open Z in
    let res = match n with
      | 0 -> Z.zero
      | 1 -> ~$ m
      | _ ->
        let n = Stdlib.(n - 1) in
        let rec apps i =
          if i <= 0 then Z.zero else
          arr.(i).(m) * Stdlib.(arr.(n - i).(m)) + apps Stdlib.(i-1) in
        let apps2 i =
          if Stdlib.(i mod 2 == 0) then
            ~$2 * apps Stdlib.(i/2 - 1) + arr.(Stdlib.(i/2)).(m) ** 2
          else ~$2 * apps Stdlib.(i/2)  in
        Stdlib.(arr.(n).(m + 1)) + apps2 n
    in arr.(n).(m) <- res in
  let rec loop1 n =
    let rec loop2 m =
      if m >= s - n then () else (fill n m; loop2 (m+1)) in
    if n >= s then () else (loop2 0; loop1 (n+1)) in
  loop1 0;
  let get n m = arr.(n).(m) in
  get

let dynamic_lambdacount_f pool s =
  let bar ~total =
    let open Progress.Line in
    list [ spinner (); bar ~style:`UTF8 total; count_to total ] in
  Progress.with_reporter (bar ~total:s) @@ fun f ->
  let open Mpf in
  let two = of_int 2 in
  let arr = Array.init s (fun i -> Array.init (s - i) (fun _ -> of_int 0)) in
  let fill (n : int) (m : int) : unit =
    let tmp1 = init () in
    let tmp2 = init () in
    let v = arr.(n).(m) in
    match n with
      | 0 -> set_si v 0
      | 1 -> set_si v m
      | _ ->
        let n = Stdlib.(n - 1) in
        let rec apps i =
          if i <= 0 then () else begin
            mul tmp1 arr.(i).(m) arr.(n - i).(m);
            add tmp2 tmp2 tmp1;
            apps (i-1)
          end in
        let apps2 i =
          set_si tmp2 0;
          if Stdlib.(i mod 2 == 0) then begin
            apps (i/2 - 1);
            mul tmp2 tmp2 two;
            mul tmp1 arr.(i/2).(m) arr.(i/2).(m);
            add tmp2 tmp2 tmp1
          end
          else begin
            apps (i/2);
            ignore (mul tmp2 tmp2 two);
          end in
        begin
          apps2 n;
          ignore (add v arr.(n).(m + 1) tmp2)
        end in
  for n = 0 to s do
    let rec loop2 m =
      if m >= s - n then () else (fill n m; loop2 (m+1)) in
    if true then
      Domainslib.Task.parallel_for ~start:0 ~finish:(s - n - 1) ~body:(fun m -> fill n m) pool
    else loop2 0;
    f 1;
  done;
  let get n m = arr.(n).(m) in
  get

let%test "check dynamic calculator correct" =
  let eff = dynamic_lambdacount 15 in
  (List.init 15 @@ fun i -> naive_lambdacount i 0) =
  (List.init 15 @@ fun i -> eff i 0)

let%test "check dynamic calculator float correct" =
  let pool = Domainslib.Task.setup_pool ~num_domains:(Domain.recommended_domain_count () - 1) () in
  Domainslib.Task.run pool @@ fun () ->
  let eff = dynamic_lambdacount_f pool 15 in
  (List.init 15 @@ fun i -> Z.to_int @@ naive_lambdacount i 0) =
  (List.init 15 @@ fun i -> Mpf.get_int @@ eff i 0)
