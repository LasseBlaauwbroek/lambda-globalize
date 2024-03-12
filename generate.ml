open Lambda
open Lambdacount

let unrank t : int -> int -> Z.t -> pure_term =
  let rec unrank n m k =
    let open Printf in
    if n = 1 then Var (Z.to_int k) else
    if k < t (n - 1) (m + 1) then Lam (unrank (n - 1) (m + 1) k) else
      let n = n - 1 in
      let rec app_term j h =
        let zl = t j m in
        let zr = t (n - j) m in
        let zt = Z.(zl * zr) in
        if zt > Z.zero && h < zt then App (unrank j m Z.(h / zr), unrank (n - j) m Z.(h mod zr))
        else app_term (j + 1) Z.(h - zt)
      in
      app_term 1 (Z.sub k (t n (m + 1)))
  in unrank

let random_term rstate t n m =
  let rec aux n m =
    if n == 1 then Var (Random.int m) else
      let rand = Mpf.init () in
      Gmp_random.Mpf.urandomb rand rstate 64;
      Mpf.mul rand rand (t n m);
      if Mpf.cmp rand (t (n - 1) (m + 1)) == -1 then Lam (aux (n - 1) (m + 1)) else
        begin
          let apps = Mpf.init () in
          Mpf.sub rand rand (t (n - 1) (m + 1));
          let n = n - 1 in
          let rec find_split j =
            Mpf.mul apps (t j m) (t (n - j) m);
            if Mpf.cmp_si apps 0 == 1 && Mpf.cmp rand apps == -1 then
              App (aux j m, aux (n - j) m)
            else begin
              Mpf.sub rand rand apps;
              find_split (j + 1)
            end
          in
          find_split 1
        end
  in
  aux n m

let linear_term n =
  let apps = List.fold_right (fun i t -> App (t, Var i)) (List.init (n - 1) (fun i -> i)) (Var (n - 1)) in
  List.init n (fun _ -> ()) |> List.fold_left (fun t () -> Lam t) apps

let linear_size n =
    if n mod 2 == 0 then (Int.shift_left 2 n + 1) / 3 else (Int.shift_left 2 n + 2) / 3

let balanced_term n =
  let rec aux n m =
    if n == 1 then Var (Random.int m) else
      if n mod 2 == 0 then Lam (aux (n - 1) (m + 1)) else
        let n = (n - 1) / 2 in
        App (aux n m, aux n m)
  in aux n 0

let balanced_size n = Int.shift_left 4 n - 2

let closed t =
  let rec free = function
    | Var i -> i
    | Lam t -> free t - 1
    | t -> fold_termf (fun i t -> max i (free t)) (-1) t
  in free t < 0

let%test "test closed" =
  closed (Lam (Var 0)) && not (closed (Lam (Var 1))) && not (closed (Lam (App (Var 1, Var 0))))

let%test "unrank closed" =
  let t = dynamic_lambdacount 15 in
  let ls = List.init 13
      (fun n -> List.init Z.(to_int (t Stdlib.(n + 2) 0 - Z.one))
          (fun k -> unrank t (n + 2) 0 (Z.of_int k))) in
  List.for_all (List.for_all closed) ls

let%test "random_term closed" =
  let pool = Domainslib.Task.setup_pool ~num_domains:(Domain.recommended_domain_count () - 1) () in
  Domainslib.Task.run pool @@ fun () ->
  let rstate = Gmp_random.init_default () in
  let t = dynamic_lambdacount_f pool 15 in
  let ls = List.init 13
      (fun n -> List.init 100
          (fun k -> random_term rstate t (n + 2) 0)) in
  List.for_all (List.for_all closed) ls

let stats ls =
  let arr = Array.of_list ls in
  Array.sort Float.compare arr;
  let length = Array.length arr in
  let min = arr.(0) in
  let max = arr.(length - 1) in
  let q1 = arr.((length - 1) / 4) in
  let q2 = arr.((length - 1) / 2) in
  let q3 = arr.((length - 1) / 4 * 3) in
  min, q1, q2, q3, max

let time f =
  let start = Unix.gettimeofday () in
  ignore (f ());
  Unix.gettimeofday () -. start
