module DB = SBDebug
module EString = ExtLib.String
module EList = ExtLib.List

(******************************************************************************)

module Basic = struct

  type ratio = (int * int)

  type mvalue =
    | MvRatio of ratio
    | MvInt of int
    | MvInts of int list

  (* piping inline function *)

  let (<<) f g x = x |> g |> f

  let (>>) f g x = x |> f |> g

  (* let get_time () = Sys.time () *)

  let get_time () = Unix.gettimeofday ()

  let identity = fun x -> x

  let fst3 (x, y, z) = x

  let snd3 (x, y, z) = y

  let thr3 (x, y, z) = z

  let max_ints xs = match xs with
    | [] -> raise (Failure "max_ints: empty list")
    | x::xs -> List.fold_left (fun acc y -> max acc y) x xs

  let min_ints xs = match xs with
    | [] -> raise (Failure "min_ints: empty list")
    | x::xs -> List.fold_left (fun acc y -> min acc y) x xs

  let mk_ratio x y = (x, y)

  let pr_ratio (x, y) = (string_of_int x) ^ "/" ^ (string_of_int y)

  let pr_mvalue mv = match mv with
    | MvInt v -> string_of_int v
    | MvRatio v -> pr_ratio v
    | MvInts vs -> vs |> List.map string_of_int |> String.concat ","

  let float_of_ratio x y = (float_of_int x) /. (float_of_int y)

end;;


module String = struct

  include String

  let exists str sub = EString.exists str sub

  let ends_with str sub = EString.ends_with str sub

end;;

module List = struct

  include List

  let rec combine3 l1 l2 l3 =
    match (l1, l2, l3) with
    | ([], [], []) -> []
    | (a1::l1, a2::l2, a3::l3) -> (a1, a2, a3) :: combine3 l1 l2 l3
    | (_, _, _) -> invalid_arg "List.combine3"

  let rec split3 = function
    | [] -> ([], [], [])
    | (x, y, z)::l ->
      let (rx, ry, rz) = split3 l in (x::rx, y::ry, z::rz)

  let exists_pair (f: 'a -> 'b -> bool) (lst1: 'a list) (lst2: 'b list) : bool =
    List.exists (fun x -> List.exists (fun y -> f x y) lst2) lst1

  let for_all_pair (f: 'a -> 'b -> bool) (lst1: 'a list) (lst2: 'b list) : bool =
    List.for_all (fun x -> List.for_all (fun y -> f x y) lst2) lst1

  let rec compare (cmp: 'a -> 'a -> int) (xs: 'a list) (ys: 'a list) : int =
    match xs, ys with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | x::xs0, y::ys0 ->
      let tmp = cmp x y in
      if (tmp !=0) then tmp else compare cmp xs0 ys0

  let sorti (cmp: 'a -> 'a -> int) (lst: 'a list) : 'a list =
    List.sort cmp lst

  let sortd (cmp: 'a -> 'a -> int) (lst: 'a list) : 'a list =
    let ncmp x y = - (cmp x y) in
    List.sort ncmp lst

  let first_nth n lst =
    let rec aux lst acc m =
      if (lst = []) || (m <= 0) then acc
      else aux (List.tl lst) (acc @ [(List.hd lst)]) (m - 1) in
    aux lst [] n

  let exclude filter lst =
    List.filter (fun x -> not (filter x)) lst

  let intersect cmp lst1 lst2 =
    List.filter (fun e ->
      (List.exists (cmp e) lst2)) lst1

  let diff cmp lst1 lst2 =
    List.filter (fun e ->
      not (List.exists (cmp e) lst2)) lst1

  let empty lst = lst = []

  let not_empty lst = lst != []

  let split_nth (n: int) (lst: 'a list) : ('a list * 'a list) =
    EList.split_nth n lst

  let extract_each (lst : 'a list) : ('a * 'a list) list =
    let rec extract head tail acc = match tail with
      | [] -> acc
      | x::xs -> extract (head @ [x]) xs (acc @ [(x, head @ xs)]) in
    extract [] lst []

  (* let extracti n lst = *)

  let cluster (cmp: 'a -> 'a -> int) (lst: 'a list) : 'a list list =
    let rec aux acc lst = match lst with
      | [] -> acc
      | hd::tl ->
        let nacc = match acc with
          | [] -> [[hd]]
          | xs::xss ->
            if (cmp (List.hd xs) hd = 0) then (hd::xs)::xss
            else [hd]::acc in
        aux nacc tl in
    aux [] (sorti cmp lst)

  let mem (cmp: 'a -> 'a -> bool) (v: 'a) (lst: 'a list) : bool =
    lst |> List.exists (fun u -> cmp u v)

  let dedup (cmp: 'a -> 'a -> bool) (lst: 'a list) : 'a list =
    lst |>
    List.fold_left (fun acc u ->
      if mem cmp u acc then acc
      else acc @ [u]) []

  let max (lst: 'a list) : 'a =
    match lst with
    | [] -> raise (Failure "max: empty list")
    | x::xs -> List.fold_left (fun acc y -> max acc y) x xs

  let fold_left_stop (fold : 'a -> 'b -> 'a)
      (stop: 'b -> bool) (init: 'a) (lst: 'b list) : 'a  =
    let rec do_fold acc xs = match xs with
      | [] -> acc
      | x::xs ->
        if (stop x) then acc
        else do_fold (fold acc x) xs in
    do_fold init lst

  let map_concat (f: 'a -> 'b list) (xs : 'a list) : 'b list =
    xs |> List.map f |> List.concat

  let count (f: 'a -> bool) (xs : 'a list) : int =
    List.fold_left (fun acc x ->
      if (f x) then acc + 1 else acc ) 0 xs

end;;

module Print = struct

  let pr_id = (fun x -> x)

  let pr_int = string_of_int

  let pr_s (s: string) = s

  let pr_lcs = String.lowercase_ascii

  let pr_ucs = String.uppercase_ascii

  let pr_float = string_of_float

  let pr_bool = string_of_bool

  let pr_b = pr_bool

  let pr_exn = Printexc.to_string

  let pr_opt f x = match x with
    | None -> "None"
    | Some y -> "Some " ^ (f y)

  let pr_space length =
    let rec space_of i =
      if (i <= 0) then ""
      else " " ^ (space_of (i - 1)) in
    space_of length

  let pr_indent indent =
    pr_space (indent * 2)

  let eq_s x y = String.compare x y = 0

  let pr_list ?(sep=", ") ?(obrace="") ?(cbrace="")
              ?(indent=0) ?(extra="") print items =
    let sindent = pr_indent indent in
    let extra =
      if (eq_s obrace "") then extra
      else if (String.exists sep "\n") then
        (pr_space (String.length obrace + 1)) ^ extra
      else extra in
    let content = match items with
      | [] -> ""
      | [u] -> print u
      | u::us ->
        let nsitems =
          let nu = print u in
          let nus = List.map (fun u -> sindent ^ extra ^ (print u)) us in
          nu::nus in
        String.concat sep nsitems in
    let obrace, cbrace =
      if not (String.exists content "\n") || (eq_s obrace "") then
        (obrace, cbrace)
      else (sindent ^ obrace ^ " ", " " ^ cbrace) in
    obrace ^ content ^ cbrace


  let pr_list_sbrace = pr_list ~obrace:"[" ~cbrace:"]"

  let pr_list_cbrace = pr_list ~obrace:"{" ~cbrace:"}"

  let pr_list_pbrace = pr_list ~obrace:"(" ~cbrace:")"

  let pr_items ?(bullet="-") ?(obrace="") ?(cbrace="") ?(extra="") print items =
    if items <> [] then
      let print x = bullet ^ " " ^ (print x) in
      pr_list ~sep:"\n" ~obrace:obrace ~cbrace:cbrace ~extra:extra print items
    else "[ ]"

  let pr_listln print items =
    pr_list ~sep:"\n" ~obrace:"[" ~cbrace:"]" print items

  let pr_args print items = pr_list ~sep:"," print items

  let pr_pair pr1 pr2 (v1, v2) =
    "(" ^ (pr1 v1) ^ ", " ^ (pr2 v2) ^ ")"

  let pr_pairs pr1 pr2 items =
    let pr (v1,v2) = "(" ^ (pr1 v1) ^ "," ^ (pr2 v2) ^ ")" in
    pr_list ~sep:";" pr items

  let pr_ints is = pr_list_sbrace pr_int is

  let pr_ids ss = pr_list_sbrace pr_id ss

  let pr_ss ss = pr_list_sbrace pr_id ss

end;;

open Print


(******************************************************************************)

(** generic module for pair *)
module Pair = struct
  type ('a, 'b) t = ('a * 'b)

  let fold f x y = (f x, f y)

  let map f (x,y) = (f x, f y)

  let map2 (f, g) (x, y) = (f x, g y)

  let reverse (x, y) = (y, x)

end;;

module Opt = struct
  type 'a t = 'a option

  let map f x = match x with
    | None -> None
    | Some x -> Some (f x)

  let iter f x = match x with
    | None -> ()
    | Some x -> (f x); ()

  let expose default = function
    | None -> default
    | Some x -> x

end;;

(******************************************************************************)

(** generic module for function *)
module Func = struct

  open Basic

  exception Timeout

  let for_all fs = fun x -> List.for_all (fun f -> f x) fs

  let exists fs = fun x -> List.exists (fun f -> f x) fs

  let for_all_not fs = fun x -> List.for_all (fun f -> not (f x)) fs

  let exists_not fs = fun x -> List.exists (fun f -> not (f x)) fs

  let apply_fst f (a, b) = f a

  let apply_snd f (a, b) = f b

  let time (f : unit -> 'a) : ('a * float) =
    let time_begin = get_time () in
    let res = f () in
    let time_end = get_time () in
    let time = time_end -. time_begin in
    (res, time)

  let record_time (f : unit -> 'a) (time: float ref) : 'a =
    let time_begin = get_time () in
    let res = f () in
    let time_end = get_time () in
    time := !time +. (time_end -. time_begin);
    res

  (* (\* timeout using thread seems to be better than timeout using signal *\) *)
  (* let timeout_opt (time: int) (f: unit -> 'a) : 'a option = *)
  (*   let ch = Event.new_channel () in *)
  (*   let tf = Thread.create (fun () -> *)
  (*     let res = f () in *)
  (*     `Result res |> Event.send ch |> Event.sync) () in *)
  (*   let timeout = Thread.create (fun () -> *)
  (*     Thread.delay (float_of_int time); *)
  (*     `Time_out |> Event.send ch |> Event.sync) () in *)
  (*   let res = *)
  (*     let first_res = ch |> Event.receive |> Event.sync in *)
  (*     let _ = try Thread.kill timeout; Thread.kill tf with _ -> () in *)
  (*     first_res in *)
  (*   match res with *)
  (*   | `Time_out -> None *)
  (*   | `Result x -> Some x *)

  let timeout_opt (time: int) (f : unit -> 'a) : 'a option =
    (* let restore handler = Sys.set_signal Sys.sigalrm handler in *)
    let restore handler = Sys.set_signal Sys.sigalrm Sys.Signal_ignore in
    let new_handler = Sys.Signal_handle (fun x ->
      print_endline ("Signal Code: " ^ (string_of_int x));
      raise Timeout) in
    let old_handler = Sys.signal Sys.sigalrm new_handler in
    try
      let _ = Unix.alarm time in
      let res = f () in
      restore old_handler ;
      Some res
    with
    | Timeout -> restore old_handler; None
    | exn -> restore old_handler; raise exn

  let timeout_default time f default =
    match timeout_opt time f with
    | Some res -> res
    | None -> default


  (* NOTE: Use fork() create many daemon processes *)
  let timeout_fork (time: int) (f: unit -> 'a) : 'a option =
    let pipe_r, pipe_w = Unix.pipe () in
    match Unix.fork () with
    | 0 ->
      let x = Some (f ()) in
      let oc = Unix.out_channel_of_descr pipe_w in
      Marshal.to_channel oc x [];
      close_out oc;
      exit 0
    | pid0 ->
      let res =
        match Unix.fork () with
        | 0 ->
          Unix.sleep time;
          let _ = try Unix.kill pid0 Sys.sigkill with
            | Unix.Unix_error (e,f,p) ->
              raise (Failure ((Unix.error_message e) ^ "|" ^ f ^ "|" ^ p))
            | e -> raise e in
          let oc = Unix.out_channel_of_descr pipe_w in
          Marshal.to_channel oc None [];
          close_out oc;
          exit 0
        | pid1 ->
          let ic = Unix.in_channel_of_descr pipe_r in
          let res = Marshal.from_channel ic in
          let _ = try Unix.kill pid1 Sys.sigkill with _ -> () in
          res in
      res

end;;


(******************************************************************************)

(** generic module for combination *)
module Comb = struct
  (** extract all possible combination of k elements from a list
      reference: https://ocaml.org/learn/tutorials/99problems.html *)
  let gen_combinations (k: int) list =
    let rec aux k acc emit = function
      | [] -> acc
      | h :: t ->
        if k = 1 then aux k (emit [h] acc) emit t
        else
          let new_emit x = emit (h :: x) in
          aux k (aux (k-1) acc new_emit t) emit t in
    let emit x acc = x :: acc in
    aux k [] emit list;;

  (** generate permutations of a list
      http://typeocaml.com/2015/05/05/permutation/ *)
  let gen_permutations list =
    let ins_all_positions x l =
      let rec aux prev acc = function
        | [] -> (prev @ [x]) :: acc |> List.rev
        | hd::tl as l -> aux (prev @ [hd]) ((prev @ [x] @ l) :: acc) tl in
      aux [] [] l
    in
    let rec permutations = function
      | [] -> []
      | x::[] -> [[x]] (* we must specify this edge case *)
      | x::xs ->
        List.fold_left (fun acc p ->
          acc @ ins_all_positions x p) [] (permutations xs)
    in
    permutations list

  (** extract all possible combinations with repetition
      of k element from a list:
      https://rosettacode.org/wiki/Combinations_with_repetitions#OCaml *)

  let gen_combinations_with_repetition (k: int) list =
    let rec gen_combs k xxs = match k, xxs with
      | 0,  _ -> [[]]
      | _, [] -> []
      | k, x::xs ->
        (List.map (fun ys -> x::ys) (gen_combs (k-1) xxs)) @ gen_combs k xs in
    gen_combs k list

  let gen_permutations_with_repetition (k: int) list =
    let rec extract k list =
      if (k <= 0) then [[]]
      else
        List.fold_left (fun acc x ->
          let nlist = (extract (k-1) list) in
          let nlist = List.map (fun l -> x::l) nlist in
          acc@nlist) [] list in
    extract k list

  let gen_cartesian (lst: 'a list list) : 'a list list =
    let rec combine xs ys =
      xs |>
      List.map (fun x -> List.map (fun y -> x @ [y]) ys) |>
      List.concat in
    let rec gen acc lst =
      match lst with
      | [] -> acc
      | x::xs -> gen (combine acc x) xs in
    match lst with
    | [] -> []
    | x::xs -> gen (List.map (fun y -> [y]) x) xs

end;;


(******************************************************************************)

module LinReg = struct

  (* https://spin.atomicobject.com/2014/06/24/gradient-descent-linear-regression/ *)

  let epsilon = 1.0e-02

  let learning_rate = 0.01

  let max_iter = 1000

  (* y = m * x + b *)
  let compute_error (m: float) (b: float) points : float =
    let total = List.fold_left (fun acc (x,y) ->
      acc +. (y -. (m *. x +. b)) ** 2.) 0. points in
    (total /. (float_of_int (List.length points)))

  let step_gradient m_cur b_cur points learning_rate =
    let m_init = 0. in
    let b_init = 0. in
    let n = float_of_int (List.length points) in
    let m_grad, b_grad = List.fold_left (fun (am, ab) (x, y) ->
      let am = am -. (2. /. n) *. x *. (y -. ((m_cur *. x) +. b_cur)) in
      let ab = ab -. (2. /. n) *. (y -. ((m_cur *. x) +. b_cur)) in
      (ab, am)) (b_init, m_init) points in
    let nm = m_cur -. (learning_rate *. m_grad) in
    let nb = b_cur -. (learning_rate *. b_grad) in
    (nm, nb)

  (* let gradient_descent_runner points b_start m_start learning_rate num_iter = *)
  (*   let rec loop ab am iter = *)
  (*     if (iter <= 0) then (ab, am) *)
  (*     else *)
  (*       let nb, nm = step_gradient ab am points learning_rate in *)
  (*       loop nb nm (iter - 1) in *)
  (*   loop b_start m_start num_iter *)

  let gradient_descent points m_start b_start learning_rate =
    let rec loop am ab ae ai =
      let nm, nb = step_gradient am ab points learning_rate in
      let error = compute_error nm nb points in
      if (abs_float (error -. ae) < epsilon) then (nm, nb)
      else if (ai > max_iter) then (nm, nb)
      else loop nm nb error (ai + 1) in
    loop m_start b_start 0. 0

  (* returns m, b of the line y = m * x + b *)
  let rec gradient_descent_series (weights : int list) =
    let pr_out (x, y) = pr_pair pr_float pr_float (x, y) in
    SBDebug.trace_1 "gradient_descent_series"
      (pr_ints, pr_out) weights
      (fun () -> gradient_descent_series_x weights)

  (* returns m, b of the line y = m * x + b *)
  and gradient_descent_series_x (weights : int list) =
    let _, points = List.fold_left (fun (ai, ap) w ->
      let p = (float_of_int ai, float_of_int w) in
      (ai+1, p::ap)) (1, []) weights in
    let m_init = 0. in
    let b_init = 0. in
    gradient_descent points m_init b_init learning_rate

  let main () =
    (* let points = *)
    (*   let data = Csv.load "data.csv" in *)
    (*   List.map (fun xs -> match xs with *)
    (*     | u::v::[] -> (float_of_string u, float_of_string v) *)
    (*     | _ -> failwith "gradient_descent: data error") data in *)
    let points = [(1., 4.);
                  (2., 3.);
                  (3., 2.);
                  (4., 2.);
                  (5., 3.);
                  (6., 2.);
                  (7., 3.);] in
    let m_init = 0. in
    let b_init = 0. in
    (* let num_iter = 1000 in *)
    let m, b = gradient_descent points m_init b_init learning_rate in
    print_endline ("m = " ^ (string_of_float m) ^ "; b = " ^ (string_of_float b))
end;;


(******************************************************************************)

(** vertex of string *)
module VertexStr = struct
  type t = string
  let compare c1 c2 = String.compare c1 c2
  let hash c = Hashtbl.hash c
  let equal c1 c2 = (String.compare c1 c2 = 0)
end

(** graph of string *)
module GraphStr = Graph.Imperative.Digraph.Concrete(VertexStr)
module GraphStrSCC = Graph.Components.Make(GraphStr)
