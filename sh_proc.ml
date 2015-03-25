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

let mapd_exists id m =
  try
    let lst = Hashtbl.find mapd id in
    if m="none" then true
    else
      List.exists (fun (e,_) -> (String.capitalize e)=m) lst
  with _ -> false
;;


(* ---------------------------------------- *)
(* Use hashtbl to record alias for modules *)
let m_alias = Hashtbl.create 100;;

let add_m_alias (alias:string) (name:string) =
  try
    let lst = Hashtbl.find  m_alias name in
    Hashtbl.replace m_alias name (alias::lst)
  with Not_found ->
      (* let () = print_endline ("Add alias "^alias) in *)
      Hashtbl.add m_alias name [alias]
;;

let is_alias name alias =
  try
    let lst = Hashtbl.find m_alias name in
    List.exists (fun e -> alias = e) lst
  with Not_found ->
      false
;;


(* ---------------------------------------- *)

let mapd_x_add_1 id m=
  let lst = Hashtbl.find mapd id in
  if (not (m=""))
  then
    List.exists (fun (a,n) -> ((String.capitalize a)=m || is_alias (String.capitalize a) m) && n=1) lst
  else
    List.exists (fun (a,n) -> n=1) lst

;;
(* let mapd_exists_with_lst id mlst = *)
(*   try *)
(*     let lst = Hashtbl.find mapd id in *)
(*     List.exists (fun e -> List.mem e mlst *)

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

let reg2 = Str.regexp "^\\([^\.]+\\)\.ml:[ \t]*Debug.no_\\([1-9]\\) *\"\\([^\"]+\\)"

let main file =
  let ff = open_in file in
  let rec aux i =
    try
      let line = input_line ff in
      (* let _ = print_endline ("start "^line) in *)
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
        let _ = print_endline ("FAIL "^line) in
        aux (i+1)
    with End_of_file ->
        begin
          (* print_endline "end of file"; *)
          (* print_endline (mapd_dupl_string_of ()) *)
        end
  in
  aux 0;;

main "cppo/dd_no2.txt";;
(* print_endline (mapd_string_of ());;  *)

(* print_endline (string_of_shell ());; *)

let rex_ml = Str.regexp "\\([^\.]+\\)\.ml"
(* let rex_ml = Str.regexp "\\(astsimp\)\.ml" *)

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


(* To complete the regular expression with the other calling cases. *)
let reg5 = Str.regexp ".*=[ \t]*\\([A-Z][_A-Za-z0-9]*\\)\.\\([^ \t]+\\)" (* *)
let reg7 = Str.regexp ".*([ \t]*\\([A-Z][_A-Za-z0-9]*\\)\.\\([^ \t]+\\)"
let reg6 = Str.regexp ".*=[ \t]*\\([a-z][_A-Za-z0-9]*\\)[ \t]+\\([^ \t]+\\)"
let reg8 = Str.regexp ".*([ \t]*\\([a-z][_A-Za-z0-9]*\\)[ \t]+\\([^ \t]+\\)"
let reg9 = Str.regexp "[ \t(]*\\([A-Z][_A-Za-z0-9]*\\)\.\\([^ \t]+\\)" (* *)
let reg10 = Str.regexp "[ \t(]*\\([a-z][_A-Za-z0-9]*\\)[ \t]+\\([^ \t]+\\)"

let reg_alias = Str.regexp "module[ \t]+\\([A-Z][_A-Za-z0-9]*\\)[ \t]*=[ \t]*\\([A-Z][_A-Za-z0-9]*\\)"

module StringPlus=
    struct
      type t = (string*int)
      let compare (a,_) (b,_)= String.compare a b
    end
module SSet = Set.Make(StringPlus);;

let process2_file f =
  let ff = open_in f in
  let output = ref SSet.empty in
  let rec aux i =
    try
      let line = input_line ff in
      (* record module alias *)
      let al = Str.string_match reg_alias line 0 in
      let () = 
        if al
        then
          let name = Str.matched_group 1 line in
          let alias = Str.matched_group 2 line in
          add_m_alias name alias
        else
          ()
      in
      let bb = Str.string_match reg5 line 0 in
      if bb then
        let m1 = Str.matched_group 1 line in
        let m2 = Str.matched_group 2 line in
        if mapd_exists m2 m1 then
          (* let () = Debug.binfo_hprint (add_str "found" (pr_list pr_id)) [m1;m2] no_pos in *)
          (* let () = print_endline line in *)
          (* let () = output:= "s/"^m1^"."^m2^"/x_add "^m1^"."^m2^"/\n"^(!output) in *)
          let () = 
            if mapd_x_add_1 m2 m1 then
              (* let () = print_endline ("x_add_1: "^m2) in *)
              output:=SSet.add ((m1^"."^m2),1) (!output)
            else
              output:=SSet.add ((m1^"."^m2),0) (!output)
          in
          aux (i+1)
        else
          aux (i+1)
      else
        let bb = Str.string_match reg6 line 0 in
        if bb then
          let m1 = Str.matched_group 1 line in
          if mapd_exists m1 "none" then
            (* let () = Debug.binfo_hprint (add_str "found 2" (pr_list pr_id)) [m1;"none"] no_pos in *)
            (* let () = print_endline line in *)
            (* let () = output:= "s/"^m1^"/x_add "^m1^"/\n"^(!output) in *)
            let () =
              if mapd_x_add_1 m1 "" then
                output := SSet.add (m1,1) (!output)
              else
                output := SSet.add (m1,0) (!output)
            in
            aux (i+1)
          else
            aux (i+1)
        else
          aux (i+1)
    with End_of_file ->
        begin
          (* print_endline ((string_of_int i)^"<-- end of file"); *)
          SSet.iter (fun (e,n) -> if n=1 then print_endline ("s/=\s*"^e^" /= x_add_1 "^e^" /") else print_endline ("s/=\s*"^e^" /= x_add "^e^" /")) (!output);
          SSet.iter (fun (e,n) -> if n=1 then print_endline ("s/(\s*"^e^" /( x_add_1 "^e^" /") else print_endline ("s/(\s*"^e^" /( x_add "^e^" /")) (!output);
        end
  in
  aux 0
;;

(* ---------------  Collect all the call sites. --------------------- *)
let new_mapd = Hashtbl.copy mapd;;
let new_mapd_string_of () =
  Hashtbl.fold (fun id lst acc -> (id^":"^((pr_list (pr_pair pr_id string_of_int)) lst))^"\n"^acc) new_mapd ""
;;

let new_mapd_exists id m =
  try
    let lst = Hashtbl.find mapd id in
    true
  with _ -> false
;;

let can_match_2 line reg =
  if Str.string_match reg line 0 then
    
    let m1 = Str.matched_group 1 line in
    let m2 = Str.matched_group 2 line in
    let () = print_endline (line^" m1:"^m1^" m2:"^m2) in
    if new_mapd_exists m2 m1 then
      let () = Hashtbl.remove new_mapd m2 in
      true
    else
      false
  else
    false
;;

let can_match_1 line reg =
  if Str.string_match reg line 0 then
    (* let () = print_endline line in *)
    let m1 = Str.matched_group 1 line in
    let () = print_endline (line^" m1:"^m1) in
    if new_mapd_exists m1 "none" then
      let () = Hashtbl.remove new_mapd m1 in
      true
    else false
  else
    false
;;

let collect_call_name_all dirlst =
  let collect_call_name f=
    let () = print_endline f in
    let ff = open_in f in
    let rec aux i=
      try
        let line = input_line ff in
        let () =
          begin
            can_match_2 line reg5;
            can_match_2 line reg7;
            can_match_2 line reg9;
            can_match_1 line reg6;
            can_match_1 line reg8;
            can_match_1 line reg10;
            ()
          end
        in
        aux (i+1)
      with End_of_file ->
          ()
    in
    aux 0
  in
  let () = List.iter (fun dir -> collect_call_name dir) dirlst in
  new_mapd_string_of ()
;;
(* let ml_files = ["fixcalc.ml"];;  *)
(* let () = print_endline (collect_call_name_all ml_files);; *)

(* List.map process2_file ml_files;; *)
let _ = process2_file Sys.argv.(1);;

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
  in
  aux 0 [];;

let rex_open = Str.regexp "open *\\([^\b]+\\)"

let open_astsimpl = find_lines "astsimp.ml" rex_open;;

(* Debug.binfo_hprint (add_str "open_astsimpl" (pr_list_ln pr_id)) open_astsimpl no_pos;; *)


