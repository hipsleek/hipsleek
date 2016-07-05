open VarGen
open Gen

(* let reg = Str.regexp "^[\#]+x-add \\([^\.]+\\)\.\([^ ]+\) \\([^.]+\\)\.ml \\([a-z].*\\\)+";; *)

(* let mapt = Hashtbl.create 10 *)

(* let rec add_2_lst e lst = *)
(*   match lst with *)
(*     | [] -> [(e,1)] *)
(*     | (a,n)::lst ->  *)
(*           if a=e then (a,n+1)::lst *)
(*           else (a,n)::(add_2_lst e lst) *)

(* let mapt_add_elem id e = *)
(*   try  *)
(*     let lst = Hashtbl.find mapt id in *)
(*     let lst = add_2_lst e lst in *)
(*      Hashtbl.replace mapt id (lst) *)
(*   with _ -> *)
(*       Hashtbl.add mapt id [(e,1)] *)

(* let mapt_string_of () = *)
(*   Hashtbl.fold (fun id lst acc -> (id^":"^((pr_list (pr_pair pr_id string_of_int)) lst))^"\n"^acc) mapt "" *)

(* let rec  main i = *)
(*   try *)
(*     let  x = read_line() in *)
(*     let bb = Str.string_match reg x 0 in *)
(*     let m1 = Str.matched_group 1 x in *)
(*     let m2 = Str.matched_group 2 x in *)
(*     let m3 = Str.matched_group 3 x in *)
(*     let () = mapt_add_elem m3 m1 in *)
(*     (\* let () = Debug.binfo_hprint (add_str "match" string_of_bool) bb no_pos in *\) *)
(*     (\* let () = Debug.binfo_hprint (add_str "str" (pr_list pr_id)) [m1;m3;m2] no_pos in *\) *)
(*     (\* print_endline (string_of_int i); *\) *)
(*     main (i+1) *)
(*   with _ -> *)
(*       begin *)
(*         print_endline "end of file"; *)
(*         print_endline (mapt_string_of ()) *)
(*       end;; *)

(* main 0;; *)

(* Debug.binfo_hprint (add_str "hello 1" pr_id) "hello" no_pos;; *)
(* Debug.binfo_hprint (add_str "hello 2" pr_id) "hello" no_pos;; *)


let rec add_2_lst e lst = e::lst

(* --------------------------------- *)
let mapd = Hashtbl.create 100000
let mapd_called = Hashtbl.create 100000

let mapd_add_elem id m =
  try
    let lst = Hashtbl.find mapd id in
    let lst = add_2_lst m lst in
    Hashtbl.replace mapd id (lst)
  with _ ->
    Hashtbl.add mapd id [m]

let find_mapd_called id =
  try
    Hashtbl.find mapd_called id
  with Not_found -> 0
;;

let mapd_exists id m =
  (* let _ = print_endline ("mapd_exists: id:"^id^" m:"^m) in *)
  try
    let lst = Hashtbl.find mapd id in
    if m="none" then
      begin
        let no = find_mapd_called id in
        if no==0 then Hashtbl.add mapd_called id 1;
        true
      end
    else
      let no = find_mapd_called id in
      let b = List.exists (fun (e,_) -> (String.capitalize e)=m) lst in
      if no>=3 then b
      else if b then (Hashtbl.replace mapd_called id 3; b)
      else  (Hashtbl.replace mapd_called id 2; b)
  with Not_found -> false
;;

let mapd_string_of () =
  Hashtbl.fold (fun id lst acc -> (id^":"^((pr_list (pr_pair pr_id string_of_int)) lst))^"\n"^acc) mapd ""
;;

let mapd_dupl_string_of () =
  Hashtbl.fold (fun id lst acc -> 
      let to_add = 
        if List.length lst > 1 then (id^":"^((pr_list (pr_pair pr_id string_of_int)) lst))^"\n"
        else ""
      in to_add^acc) mapd ""
;;
(* ---------------------------------- *)



let mapd_called_string_of n =
  if n=0 then 
    Hashtbl.fold (fun id v acc -> 
        if Hashtbl.mem mapd_called id then acc
        else id::acc) mapd []
  else
    Hashtbl.fold (fun id v acc -> 
        if v=n then id::acc else acc) mapd_called []

(* 0 - not called *)
(* 1 - called without module name *)
(* 2 - called with wrong module name *)
(* 3 - called with correct module name *)


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



let string_of_shell () =
  let pr_one id (modname,_) =
    let new_modname = (String.capitalize modname) in
    "$EX "^new_modname^" "^id^"\n"
  in
  Hashtbl.fold (fun id lst acc -> ((List.fold_left (fun s e -> s^(pr_one id e)) "" lst)^acc)) mapd ""
;;



let reg2 = Str.regexp "^\\([^\.]+\\)\.ml:[ \t]*Debug.no_\\([1-9]\\) *\"\\([^\"]+\\)"

(* Initialize mapd with information in dd_no2.txt *)
(* mapd : (id -> (module name, number)). Notice that module name is in lower case. *)
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
        );
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
  aux 0
;;


let reg_module_point = Str.regexp "[A-Za-z_0-9]+([\.:]):*[ \t]*\\([a-z0-9_]+\\)";;
let reg_splitter = Str.regexp "[^A-Za-z_0-9]";;
let clean_mapd () =
  let filter str lst =
    let strlst = Str.split reg_splitter str in
    let () = Hashtbl.remove mapd str in
    Hashtbl.add mapd (List.nth (strlst) ((List.length strlst)-1)) lst
    (* if Str.string_match reg_module_point str 0 then *)
    (*   let fun_name = Str.matched_group 1 str in *)
    (*   let () = Hashtbl.remove mapd str in *)
    (*   Hashtbl.add mapd (String.trim fun_name) lst *)
    (* else *)
    (*   let () = Hashtbl.remove mapd str in *)
    (*   Hashtbl.add mapd (String.trim str) lst *)
  in
  Hashtbl.iter (fun id lst -> filter id lst) mapd
;;



let rex_ml = Str.regexp "\\([^\.]+\\)\.ml";;
(* let rex_ml = Str.regexp "\\(pi\\)\.ml" *)

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



(* regular expressions that can match two groups *)
let reg2_1 = Str.regexp ".*=[ \t]*\\([A-Z][_A-Za-z0-9]*\\)\.\\([^ \t]+\\)";;
let reg2_2 = Str.regexp ".*([ \t]*\\([A-Z][_A-Za-z0-9]*\\)\.\\([^ \t]+\\)";;
let reg2_3 = Str.regexp "[ \t(]*\\([A-Z][_A-Za-z0-9]*\\)\.\\([^ \t]+\\)";;
let reg2_4 = Str.regexp ".*fun.*->[ \t(]*\\([A-Z][_A-Za-z0-9]*\\)\.\\([^ \t]+\\)";;
let reg2_5 = Str.regexp ".*then[ \t]+[ \t(]*\\([A-Z][_A-Za-z0-9]*\\)\.\\([^ \t]+\\)";;
let reg2_6 = Str.regexp ".*x_add[_1]* \\([A-Z][_A-Za-z0-9]*\\)\.\\([^ \t]+\\)";;

(* regular expressions that can match only one group *)
let reg1_1 = Str.regexp ".*=[ \t]*\\([a-z][_A-Za-z0-9]*\\)[ \t]+\\([^ \t]+\\)";;
let reg1_2 = Str.regexp ".*([ \t]*\\([a-z][_A-Za-z0-9]*\\)[ \t]+\\([^ \t]+\\)";;
let reg1_3 = Str.regexp "[ \t(]*\\([a-z][_A-Za-z0-9]*\\)[ \t]+\\([^ \t]+\\)";;
let reg1_4 = Str.regexp ".*fun.*->[ \t(]*\\([a-z][_A-Za-z0-9]*\\)[ \t]+\\([^ \t]+\\)";;
let reg1_5 = Str.regexp ".*then[ \t]+[ \t(]*\\([a-z][_A-Za-z0-9]*\\)[ \t]+\\([^ \t]+\\)";;


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

let can_match matched_group_num reg str =
  (* let () = print_endline ("can_match: "^str^(string_of_int matched_group_num)) in *)
  let rec helper num str =
    if num = 0 then []
    else
      (helper (num-1) str)@[Str.matched_group num str]
  in
  if Str.string_match reg str 0
  then
    (* let _ = print_endline ("Matched! "^str) in *)
    let lst = helper matched_group_num str in
    (* let () = print_endline ((pr_list (fun x -> x)) lst) in *)
    lst
  else
    []
;;

let can_match_and_exist_def matched_group_num reg str:(bool * (string list)) =
  let matched_group = can_match matched_group_num reg str in
  if List.length matched_group = 0
  then (false,[])
  else
  if List.length matched_group = 1 then
    (mapd_exists (List.nth matched_group 0) "none",matched_group)
  else
  if List.length matched_group = 2 then
    (mapd_exists (List.nth matched_group 1) (List.nth matched_group 0),matched_group)
  else
    failwith "can_match_and_exist_def: Invalid list length 2"
;;

let rec can_match_and_exist_def_lst matched_group_num reglst str:(bool * (string list)) =
  match reglst with
  | h::rest ->
    let (b,res) = can_match_and_exist_def matched_group_num h str in
    if b
    then (b,res)
    else can_match_and_exist_def_lst matched_group_num rest str
  | [] ->
    (false, [])
;;

let check_call_sites f =
  (* let () = print_endline ("check_call_sites: "^f) in *)
  let ff = open_in f in
  let output = ref SSet.empty in
  let reglst_1 = [reg1_1;reg1_2;reg1_3;reg1_4;reg1_5] in
  let reglst_2 = [reg2_1;reg2_2;reg2_3;reg2_4;reg2_5;reg2_6] in
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
      let (can_match_b_2,matched_group_2) = can_match_and_exist_def_lst 2 reglst_2 line in
      begin
        if can_match_b_2
        then
          let (fun_name,module_name) = (List.nth matched_group_2 1,List.nth matched_group_2 0) in
          let x_add_tag = if mapd_x_add_1 fun_name module_name then 1 else 0 in
          output:= SSet.add ((module_name^"."^(fun_name)),x_add_tag) (!output)
        else
          let (can_match_b_1,matched_group_1) = can_match_and_exist_def_lst 1 reglst_1 line in
          if can_match_b_1
          then
            let fun_name = List.nth matched_group_1 0 in
            let x_add_tag = if mapd_x_add_1 fun_name "" then 1 else 0 in
            ()
            (* output := SSet.add (fun_name,x_add_tag) (!output) *)
      end;
      aux (i+1)
    with End_of_file ->
      begin
        SSet.iter (fun (e,n) -> if n=1 then print_endline ("s/=\s*"^e^" /= x_add_1 "^e^" /") else print_endline ("s/=\s*"^e^" /= x_add "^e^" /")) (!output);
        (* SSet.iter (fun (e,n) -> if n=1 then print_endline ("s/(\s*"^e^" /( x_add_1 "^e^" /") else print_endline ("s/(\s*"^e^" /( x_add "^e^" /")) (!output); *)
      end
  in
  aux 0
;;

let reg3_xadd = Str.regexp ".*x_add [A-Z][_A-Za-z0-9]*\.\\([a-z][_A-Za-z0-9]*\\)";;
let reg3_xadd = Str.regexp ".*x_add \\([A-Z][_A-Za-z0-9]*\\)\.";;
let reg3_xadd = Str.regexp ".*x_add(_1)? \\(TP\.simplify_a\\)";;

let can_match_and_exist_def0 matched_group_num reg str:(bool * (string list)) =
  let matched_group = can_match matched_group_num reg str in
  if List.length matched_group = 0
  then (false,[])
  else
    (true,matched_group)

let locate_call_sites reglst f =
  (* let () = print_endline ("check_call_sites: "^f) in *)
  let ff = open_in f in
  let output = ref SSet.empty in
  (* let reglst_1 = [reg3_xadd] in *)
  let rec aux i =
    try
      let line = input_line ff in
      (* record module alias *)
      let (can_match_b_2,matched_group_2) = can_match_and_exist_def0 1 reglst line in
      begin
        if can_match_b_2
        then
          print_endline line
          (* else print_endline ("no"^line) *)
      end;
      aux (i+1)
    with End_of_file ->
      begin
        print_endline "finished locate_call_sites"
        (* SSet.iter (fun (e,n) -> if n=1 then print_endline ("s/=\s*"^e^" /= x_add_1 "^e^" /") else print_endline ("s/=\s*"^e^" /= x_add "^e^" /")) (!output); *)
        (* SSet.iter (fun (e,n) -> if n=1 then print_endline ("s/(\s*"^e^" /( x_add_1 "^e^" /") else print_endline ("s/(\s*"^e^" /( x_add "^e^" /")) (!output); *)
      end
  in
  aux 0
;;

(* locate_call_sites reg3_xadd "astsimp.ml";; *)

(* (\* *\) *)
(* let process2_file f = *)
(*   let ff = open_in f in *)
(*   let output = ref SSet.empty in *)
(*   let rec aux i = *)
(*     try *)
(*       let line = input_line ff in *)
(*       (\* record module alias *\) *)
(*       let al = Str.string_match reg_alias line 0 in *)
(*       let () = *)
(*         if al *)
(*         then *)
(*           let name = Str.matched_group 1 line in *)
(*           let alias = Str.matched_group 2 line in *)
(*           add_m_alias name alias *)
(*         else *)
(*           () *)
(*       in *)
(*       let bb = Str.string_match reg5 line 0 in *)
(*       if bb then *)
(*         let m1 = Str.matched_group 1 line in *)
(*         let m2 = Str.matched_group 2 line in *)
(*         if mapd_exists m2 m1 then *)
(*           let () = *)
(*             if mapd_x_add_1 m2 m1 then *)
(*               output:=SSet.add ((m1^"."^m2),1) (!output) *)
(*             else *)
(*               output:=SSet.add ((m1^"."^m2),0) (!output) *)
(*           in *)
(*           aux (i+1) *)
(*         else *)
(*           aux (i+1) *)
(*       else *)
(*         let bb = Str.string_match reg6 line 0 in *)
(*         if bb then *)
(*           let m1 = Str.matched_group 1 line in *)
(*           if mapd_exists m1 "none" then *)
(*             (\* let () = Debug.binfo_hprint (add_str "found 2" (pr_list pr_id)) [m1;"none"] no_pos in *\) *)
(*             (\* let () = print_endline line in *\) *)
(*             (\* let () = output:= "s/"^m1^"/x_add "^m1^"/\n"^(!output) in *\) *)
(*             let () = *)
(*               if mapd_x_add_1 m1 "" then *)
(*                 output := SSet.add (m1,1) (!output) *)
(*               else *)
(*                 output := SSet.add (m1,0) (!output) *)
(*             in *)
(*             aux (i+1) *)
(*           else *)
(*             aux (i+1) *)
(*         else *)
(*           aux (i+1) *)
(*     with End_of_file -> *)
(*         begin *)
(*           (\* print_endline ((string_of_int i)^"<-- end of file"); *\) *)
(*           SSet.iter (fun (e,n) -> if n=1 then print_endline ("s/=\s*"^e^" /= x_add_1 "^e^" /") else print_endline ("s/=\s*"^e^" /= x_add "^e^" /")) (!output); *)
(*           SSet.iter (fun (e,n) -> if n=1 then print_endline ("s/(\s*"^e^" /( x_add_1 "^e^" /") else print_endline ("s/(\s*"^e^" /( x_add "^e^" /")) (!output); *)
(*         end *)
(*   in *)
(*   aux 0 *)
(* ;; *)


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

let pr_len lst = string_of_int (List.length lst)
let status () =
  let () = Debug.binfo_hprint (add_str "called 3\n" pr_len) (mapd_called_string_of 3) no_pos in
  let () = Debug.binfo_hprint (add_str "called 2\n" pr_len) (mapd_called_string_of 2) no_pos in
  let () = Debug.binfo_hprint (add_str "called 1\n" pr_len) (mapd_called_string_of 1) no_pos in
  let () = Debug.binfo_hprint (add_str "called 0\n" pr_len) (mapd_called_string_of 0) no_pos in
  ();;


(* EXECUTING *)
main "cppo/dd_no2.txt";;

clean_mapd ();;

(* let _ = List.iter (fun e ->  (check_call_sites e; status())) ml_files;; *)
let _ = check_call_sites Sys.argv.(1);;

(* let () = Debug.binfo_hprint (add_str "called 0\n" (pr_list pr_id)) (mapd_called_string_of 0) no_pos ;; *)



(* let count_lines f = *)
(*   let ff = open_in f in *)
(*   let rec aux i = *)
(*     try *)
(*       let line = input_line ff in *)
(*       aux (i+1) *)
(*     with _ -> i in *)
(*   aux 0;; *)

(* let list_ln = List.map (fun f -> (f,count_lines f)) ml_files;; *)

(* Debug.binfo_hprint (add_str "list_ln" (pr_list_ln (pr_pair pr_id string_of_int))) list_ln  no_pos;; *)

(* let find_lines fn rex = *)
(*   let ff = open_in fn in *)
(*   let rec aux i acc = *)
(*     try *)
(*       let line = input_line ff in *)
(*       try *)
(*         let bb = Str.string_match rex line 0 in *)
(*         let m1 = Str.matched_group 1 line in *)
(*         aux (i+1) (m1::acc) *)
(*       with _ -> aux i acc *)
(*     with _ -> acc *)
(*   in *)
(*   aux 0 [];; *)

(* let rex_open = Str.regexp "open *\\([^\b]+\\)" *)

(* let open_astsimpl = find_lines "astsimp.ml" rex_open;; *)

(* Debug.binfo_hprint (add_str "open_astsimpl" (pr_list_ln pr_id)) open_astsimpl no_pos;; *)


