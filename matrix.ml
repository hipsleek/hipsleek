open Gen.Basic

(* This module is used to solve linear equation set *)

let print_lst pr lst =
  "["^(List.fold_left (fun r item -> r^" "^(pr item)^" ") "" lst)^"]"
;;


let print_matrix pr input =
  List.fold_left (fun r line -> r^"\n"^(print_lst pr line)) "" input
;;

let is_int v =
  v = (snd (modf v))
;;

let turn_matrix pr input =
  List.map (
    fun line->
      List.map (fun x -> pr x) line
  ) input
;;

let int_matrix_to_float = turn_matrix float_of_int;;
let float_matrix_to_int = turn_matrix int_of_float;;

(* input is a list of list *)
(* index starts from 0 *)
let gaussian_elimination input =
  let get_target input used index=
    let rec get_target_helper input used index choose =
      match input with
      | h ::rest ->
        if List.exists (fun x -> x=choose) used
        then
          let (r,matrix) = get_target_helper rest used index (choose+1) in
          (r,h::matrix)
        else
          (* Not been chosen yet *)
          if not (List.nth h index = (float_of_int 0))
          then
            let target_value = List.nth h index in
            (choose, (List.map (fun x -> x/.target_value) h)::rest)
          else
            let (r,matrix) = get_target_helper rest used index (choose+1) in
            (r,h::matrix)
      | [] -> (-1,input)
    in
    get_target_helper input used index 0
  in
  let eliminate input target index=
    let rec eliminate_helper input target_line index cur =
      match input with
      | h::rest ->
        if cur = target
        then h::(eliminate_helper rest target_line index (cur+1))
        else
          let factor = (List.nth h index) in
          let new_h = List.map2 (fun hi ti -> hi -. ti*.factor) h target_line in
          new_h::(eliminate_helper rest target_line index (cur+1))
      | [] -> []
    in
    let target_line = List.nth input target in
    eliminate_helper input target_line index 0
  in
  let rec iterate_helper input total used cur =
    if cur = total
    then input
    else
      let (target_num,new_input) = get_target input used cur in
      (*let () = print_endline ("new_input\n"^(print_matrix string_of_float new_input)) in*)
      if target_num = -1
      then
        iterate_helper new_input total used (cur+1)
      else
        let el_output = eliminate new_input target_num cur in
        (*let () = print_endline ("el_output\n"^(print_matrix string_of_float el_output)) in*)
        iterate_helper el_output total (target_num::used) (cur+1)
  in
  let num_of_lines = List.length input in
  if num_of_lines = 0
  then []
  else
    let num_of_variables = (List.length (List.nth input 0)) - 1 in
    iterate_helper input num_of_variables [] 0
;;

let gaussian_elimination_int input =
  gaussian_elimination (int_matrix_to_float input)
;;



(*print_endline (print_matrix string_of_int input1);;*)

let test input =
  let () = print_endline ("input:\n"^(print_matrix string_of_float input)) in
  let output = gaussian_elimination input in
  print_endline ("output:\n"^(print_matrix string_of_float output))
;;

let input1 = [[1;1;2];[1;2;3]];;
let input2 = [ [1;3;-2;5];
               [3;5;6;7];
               [2;4;3;8]
             ];;
let input3 = [ [2;1;-1;8];
               [-3;-1;2;-11];
               [-2;1;2;-3]
             ];;

let input4 = [ [1;1;0;2];
               [0;1;1;3]
             ];;


(*let input1 = [[1;2;3;4;5];[1;2;3;4;5]];;*)

(*test (int_matrix_to_float input4);;*)


let extract_answer input =
  let rec find_pos line cur =
    match line with
    | h::rest ->
      (
        if h=1.0
        then cur
        else find_pos rest (cur+1)
      )
    | [] -> -1
  in
  let has_solution input =
    match (List.rev input) with
    | h::rest ->
      let c = List.fold_left (fun r i -> if i=0. then r else r+1) 0 rest in
      if c=1
      then true
      else false
    | [] -> false
  in
  let extract_anwer_helper line =
    let sum = List.fold_left (fun r i -> r+.i) 0. line in
    let last = List.nth line ((List.length line)-1) in
    if has_solution line && is_int last
    then
      let p = find_pos line 0 in
      if p = -1 then None
      else
        Some (p,int_of_float last)
    else
      None
  in
  List.fold_left (
    fun r line ->
      match extract_anwer_helper line with
      | None -> r
      | Some a -> a::r
  ) [] input
;;

let solve_equation input =
  if true (* !Globals.oc_matrix_eqn *)
  then
    extract_answer (gaussian_elimination_int input)
  else
    []
;;

let solve_equation input =
  let pr1 = pr_list (pr_list string_of_int) in
  let pr2 = pr_list (pr_pair string_of_int string_of_int) in
  Debug.no_1 "solve_equation" pr1 pr2 solve_equation input 
