(* interpolant solver by Shengyi Wang*)
let (--) i j = 
  let rec aux n acc =
    if n < i then acc else aux (n-1) (n :: acc)
  in aux j []

let rec sublist b e l = 
  match l with
    [] -> failwith "sublist"
  | h :: t -> 
     let tail = if e=0 then [] else sublist (b-1) (e-1) t in
     if b>0 then tail else h :: tail

let write_interpolant filename intplts=
  let oc = open_out filename in
  List.iter (fun x -> Printf.fprintf oc "%s\n" x) intplts;
  close_out oc;;

let read_interpolant filename =
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; []
  with End_of_file ->
    close_in chan;
    List.rev !lines ;;

let gen_interpolant (ante:Cpure.formula) (conseq:Cpure.formula) : bool = 
  let (pr_weak,pr_strong) = Cpure.drop_complex_ops in
  let fml_str = Smtsolver.to_smt pr_weak pr_strong ante (Some conseq) Smtsolver.Z3 in
  (* let _ = Printf.printf "%s\n" fml_str in *)
  let formula_list = Str.split (Str.regexp "\n") fml_str in
  let assert_regexp = Str.regexp "(assert .+" in
  let (asserts, nonasserts) = List.partition (fun x -> Str.string_match assert_regexp x 0) formula_list in
  let nonasserts = List.append ["(set-option :print-success false)";"(set-option :produce-proofs true)";"(set-logic QF_LIA)"] nonasserts in
  let nonasserts = sublist 0 (List.length nonasserts - 2) nonasserts in
  let ass_len = String.length "(assert " in
  let ass_not_len = String.length "(assert (not " in
  let ante_list = List.rev (List.tl (List.rev asserts)) in
  let conseq_alone = List.hd (List.rev asserts) in
  let ante_list = List.map (fun x -> String.sub x ass_len ((String.length x)- ass_len - 1)) ante_list in
  let conseq_alone = String.sub conseq_alone ass_not_len ((String.length conseq_alone)- ass_not_len - 2) in
  let asserts = List.append ante_list [conseq_alone] in
  let asserts = List.map2 (fun x i -> "(assert (! " ^ x ^ " :named IP_" ^ (string_of_int i)^"))") asserts (1--(List.length asserts)) in
  let formula_list = List.append nonasserts asserts in
  let ips = List.map (fun x -> "IP_"^(string_of_int x)) (1--(List.length asserts)) in
  let intplt_str = "(get-interpolants "^ (String.concat " " ips)^")" in
  let formula_list = List.append formula_list ["(check-sat)"; intplt_str] in
  let _ = write_interpolant "interpolant.input" formula_list in
  let _ = Unix.system "java -jar smtinterpol.jar interpolant.input > interpolant.out" in
  let result = read_interpolant "interpolant.out" in
  let _ = List.map (fun x -> Printf.printf "%s\n" x) result in
  true

