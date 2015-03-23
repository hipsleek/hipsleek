open VarGen
open Gen

let reg = Str.regexp "^[\#]+x-add \\([^\.]+\\)\.\([^ ]+\) \\([^.]+\\)\.ml \\([a-z].*\\)+";;

let mapt = Hashtbl.create 10

let rec add_2_lst e lst =
  match lst with
    | [] -> [(e,1)]
    | (a,n)::lst -> 
          if a=e then (a,n+1)::lst
          else (a,n)::(add_2_lst e lst)
  
let mapt_add_elem id e =
  try 
    let lst = Hashtbl.find mapt id in
    let lst = add_2_lst e lst in
     Hashtbl.replace mapt id (lst)
  with _ ->
      Hashtbl.add mapt id [(e,1)]

let mapt_string_of () =
  Hashtbl.fold (fun id lst acc -> (id^":"^((pr_list (pr_pair pr_id string_of_int)) lst))^"\n"^acc) mapt ""

let rec  main i =
  try
    let  x = read_line() in
    let bb = Str.string_match reg x 0 in
    let m1 = Str.matched_group 1 x in
    let m2 = Str.matched_group 2 x in
    let m3 = Str.matched_group 3 x in
    let () = mapt_add_elem m3 m1 in
    (* let () = Debug.binfo_hprint (add_str "match" string_of_bool) bb no_pos in *)
    (* let () = Debug.binfo_hprint (add_str "str" (pr_list pr_id)) [m1;m3;m2] no_pos in *)
    (* print_endline (string_of_int i); *)
    main (i+1)
  with _ ->
      begin
        print_endline "end of file";
        print_endline (mapt_string_of ())
      end;;

(* main 0;; *)

(* Debug.binfo_hprint (add_str "hello 1" pr_id) "hello" no_pos;; *)
(* Debug.binfo_hprint (add_str "hello 2" pr_id) "hello" no_pos;; *)

let mapd = Hashtbl.create 100000

let rec add_2_lst e lst = e::lst
  (* match lst with *)
  (*   | [] -> [(e,1)] *)
  (*   | (a,n)::lst ->  *)
  (*         if a=e then (a,n+1)::lst *)
  (*         else (a,n)::(add_2_lst e lst) *)
  
let mapd_add_elem id m =
  try 
    let lst = Hashtbl.find mapd id in
    let lst = add_2_lst m lst in
     Hashtbl.replace mapd id (lst)
  with _ ->
      Hashtbl.add mapd id [m]

let mapd_string_of () =
  Hashtbl.fold (fun id lst acc -> (id^":"^((pr_list (pr_pair pr_id string_of_int)) lst))^"\n"^acc) mapd ""

let string_of_shell () =
  let pr_one id (modname,_) =
    let new_modname = (String.capitalize modname) in
    "$EX "^new_modname^" "^id^"\n"
  in
  Hashtbl.fold (fun id lst acc -> ((List.fold_left (fun s e -> s^(pr_one id e)) "" lst)^acc)) mapd ""
;;

let mapd_dupl_string_of () =
  Hashtbl.fold (fun id lst acc -> 
      let to_add = 
        if List.length lst > 1 then (id^":"^((pr_list (pr_pair pr_id string_of_int)) lst))^"\n"
        else ""
      in to_add^acc) mapd ""

let reg2 = Str.regexp "^\\([^\.]+\\)\.ml: *Debug.no_\\([1-9]\\) *\"\\([^\" ]+\\)"

let main file =
  let ff = open_in file in
  let rec aux i =
    try
      let line = input_line ff in
      let _ = print_endline ("start "^line) in
      let bb = Str.string_match reg2 line 0 in
      if bb then
        let m1 = Str.matched_group 1 line in
        let m2 = Str.matched_group 2 line in
        let m3 = Str.matched_group 3 line in
        let () = mapd_add_elem m3 (m1,int_of_string m2) in
        (if (not bb) then
          let _ = print_endline line in
          Debug.winfo_pprint line no_pos
        else
          ()
        )
        (* Debug.binfo_hprint (add_str "str" (pr_list pr_id)) [m1;m2;m3] no_pos) *);
      (* print_endline (string_of_int i); *)
        aux (i+1)
      else
        aux (i+1)
    with End_of_file ->
        begin
          print_endline "end of file";
          print_endline (mapd_dupl_string_of ())
        end
  in
  aux 0;;

main "cppo/dd_no2.txt";;

print_endline (mapd_string_of ());; 

print_endline (string_of_shell ());;

let rex_ml = Str.regexp "\\([^\.]+\\)\.ml"

let read_dir dir rex =
  let arr_fn = Sys.readdir dir in
  let lst = Array.to_list arr_fn in
  let lst = List.filter (fun s ->
      try
        let bb = Str.string_match rex s 0 in
        let m1 = Str.matched_group 1 s in
        (* print_endline  (s^"==>"^m1^"**"); *)
        ((String.length m1)+3) = (String.length s)
      with _ -> false
  ) lst in
  (* let () = Debug.binfo_hprint (add_str "str" (pr_list pr_id)) lst  no_pos in *)
  lst
  ;;

let ml_files = read_dir "." rex_ml

let count_lines f =
  let ff = open_in f in
  let rec aux i =
    try
      let line = input_line ff in
      aux (i+1)
    with _ -> i in
  aux 0;;

(* let list_ln = List.map (fun f -> (f,count_lines f)) ml_files;; *)

(* Debug.binfo_hprint (add_str "list_ln" (pr_list_ln (pr_pair pr_id string_of_int))) list_ln  no_pos;; *)

let find_lines fn rex =
  let ff = open_in fn in
  let rec aux i acc =
    try
      let line = input_line ff in
      try
        let bb = Str.string_match rex line 0 in
        let m1 = Str.matched_group 1 line in
        aux (i+1) (m1::acc)
      with _ -> aux i acc
    with _ -> acc 
  in aux 0 [];;

let rex_open = Str.regexp "open *\\([^\b]+\\)"

let open_astsimpl = find_lines "astsimp.ml" rex_open;;

(* Debug.binfo_hprint (add_str "open_astsimpl" (pr_list_ln pr_id)) open_astsimpl no_pos;; *)


