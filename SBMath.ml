open SBLib.Basic
open SBLib.Print

module DB = SBDebug



let average_int (xs: int list) : int =
  let total = List.fold_left (fun acc x -> acc + x) 0 xs in
  total / (List.length xs)

let average_float (xs: float list) : float =
  let total = List.fold_left (fun acc x -> acc +. x) 0. xs in
  total /. (float_of_int  (List.length xs))

let gcd (xs: int list) : int =
  let rec gcd2 a b =
    if b = 0 then a
    else gcd2 b (a mod b) in
  match xs with
  | [] -> failwith "gcd: not expect empty list"
  | u::us -> List.fold_left (fun acc v -> gcd2 acc v) u us

let lcm (xs: int list) : int =
  let rec lcm2 a b = (a / (gcd [a; b])) * b in
  match xs with
  | [] -> failwith "lcm: not expect empty list"
  | u::us -> List.fold_left (fun acc v -> lcm2 acc v) u us


module Matrix = struct

  exception Done

  let make (n: int) (m: int) : int array array =
    Array.make_matrix n m 0

  let swap_row (m : int array array) (i: int) (j: int) : unit =
    let tmp = m.(i) in
    m.(i) <- m.(j);
    m.(j) <- tmp

  let store_row (m: int array array) (r: int array) (i: int) : unit =
    m.(i) <- r

  let mult_row (r: int array) (c: int) : int array =
    Array.map (fun x -> c * x) r

  let div_row (r: int array)  (c: int) : int array =
    Array.map (fun x -> x / c) r

  let add_row (r1: int array) (r2: int array) : int array =
    Array.map2 (fun x y -> x + y) r1 r2

  let subt_row (r1: int array) (r2: int array) : int array =
    Array.map2 (fun x y -> x - y) r1 r2

  let pr_row (r: int array) : string =
    r |>
    Array.fold_left (fun acc x -> acc ^ (string_of_int x) ^ " " ) "" |>
    String.trim

  let pr_matrix (m: int array array) : string =
    m |>
    Array.fold_left (fun acc r -> acc ^ (pr_row r) ^ "\n") "" |>
    fun s -> "[\n" ^ (String.trim s) ^ "\n]"

  let gauss_transform_augmented_matrix (m: int array array) : int array array =
    (* pre-processing each row *)
    let preprocess_row (r: int array) : int array =
      let g = r |> Array.to_list |> gcd in
      if (g = 1 || g = -1 || g = 0) then r
      else div_row r g in
    (* pre-processing each row *)
    let postprocess_row (r: int array) : int array =
      let g = r |> Array.to_list |> gcd in
      if (g = 1 || g = -1 || g = 0) then r
      else div_row r g in
    let rec rearrange_nonzero_row m row1 row2 col =
      if (row2 >= Array.length m) then m
      else if m.(row2).(col) != 0 then let _ = swap_row m row1 row2 in m
      else rearrange_nonzero_row m row1 (row2 + 1) col in
    (* eliminate column to transform the matrix into triangular form *)
    let rec transform_lower_triangle (row: int) (col: int) m : int array array =
      if (Array.length m <= 0) then m
      else if (row >= Array.length m) || (col >= Array.length m.(0)) then m
      else
        let m = rearrange_nonzero_row m row row col in
        if (m.(row).(col) = 0) then
          transform_lower_triangle row (col + 1) m
        else (
          for row2 = row + 1 to (Array.length m) - 1 do
            if (m.(row).(col) != 0) && (m.(row2).(col) != 0) then (
              let k = lcm [m.(row).(col); m.(row2).(col)] in
              let c, c2 = k / m.(row).(col), k / m.(row2).(col) in
              let mrow = subt_row (mult_row m.(row) c) (mult_row m.(row2) c2) in
              store_row m mrow row2;)
          done;
          transform_lower_triangle (row + 1) (col + 1) m) in
    (* eliminate column to transform the matrix into triangular form *)
    let rec transform_upper_triangle (row: int) (col: int) m : int array array =
      if (Array.length m <= 0) then m
      else if (row >= Array.length m) || (col >= Array.length m.(0)) then m
      else if (m.(row).(col) = 0) then
        transform_upper_triangle row (col + 1) m
      else (
        for row2 = row + 1 to (Array.length m) - 1 do
          if (m.(row).(col) != 0) && (m.(row2).(col) != 0) then (
            let k = lcm [m.(row).(col); m.(row2).(col)] in
            let c, c2 = k / m.(row).(col), k / m.(row2).(col) in
            let mrow = subt_row (mult_row m.(row) c) (mult_row m.(row2) c2) in
            store_row m mrow row);
        done;
        transform_upper_triangle (row + 1) (col + 1) m) in
    (* main procedure *)
    m |>
    (fun m -> DB.nhprint "=== Input:\n" pr_matrix m; m) |>
    Array.map (fun r -> preprocess_row r) |>
    (fun m -> DB.nhprint "=== Pre-process:\n" pr_matrix m; m) |>
    transform_lower_triangle 0 0 |>
    (fun m -> DB.nhprint "=== Transform lower triangle:\n" pr_matrix m; m) |>
    transform_upper_triangle 0 0 |>
    (fun m -> DB.nhprint "=== Transform upper triangle:\n" pr_matrix m; m) |>
    Array.map (fun r -> postprocess_row r) |>
    (fun m -> DB.nhprint "=== Post-process:\n" pr_matrix m; m) |>
    identity

end;;

(* let _ = *)
(*   (\* let m = Matrix.make 3 3 in *\) *)
(*   (\* let m = [|[|1;2;1;0|]; [|1;1;1;0|]; [|1;3;1;0|]|] in *\) *)
(*   (\* let m = [|[|1;2;1;3|]; [|1;1;1;2|]; [|1;3;-1;6|]|] in *\) *)
(*   let m = [|[|1;2;1;1|]; [|1;1;1;2|]; [|1;3;1;1|]; [|1;-1;1;2|]; [|1;-3;1;6|]|] in *)
(*   let n = Matrix.gauss_transform_augmented_matrix m in *)
(*   n *)
