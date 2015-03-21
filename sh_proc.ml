open VarGen
open Gen

let reg = Str.regexp "^[\#]+x-add \\([^\.]+\\)\.\([^ ]+\) \\([^.]+\\)\.ml \\([a-z].*\\)+";;

let mapt = Hashtbl.create 10

let mapt_add_elem id e =
  try 
    let lst = Hashtbl.find mapt id in
    if List.exists (fun x -> x=e) lst then ()
    else Hashtbl.replace mapt id (e::lst)
  with _ ->
      Hashtbl.add mapt id [e]

let mapt_string_of () =
  Hashtbl.fold (fun id lst acc -> (id^":"^((pr_list pr_id) lst))^"\n"^acc) mapt ""

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

main 0;;

  
