#include "xdebug.cppo"
open Globals
open Gen.Basic
open VarGen

let wrap_infer_inv f a b =
  let flag = !is_inferring in
  is_inferring := true;
  try
    let res = f a b in
    is_inferring := flag;
    res
  with _ as e ->
    (is_inferring := flag;
     raise e)

let wrap_exception ?(msg="") dval f e =
  try
    f e
  with _ -> 
    begin
      if msg!="" then print_endline_quiet ("Exception :"^msg);
      dval
    end 

let wrap_exc_as_false ?(msg="") f e = wrap_exception ~msg:msg false f e

let wrap_num_disj f n a b c d =
  let old_disj = !fixcalc_disj in
  fixcalc_disj := max n old_disj;
  try
    let res = f a b c d in
    fixcalc_disj := old_disj;
    res
  with _ as e ->
    (fixcalc_disj := old_disj;
     raise e)

let wrap_under_baga f a =
  let flag = !do_under_baga_approx in
  do_under_baga_approx := true;
  try
    let res = f a in
    (* restore flag do_classic_frame_rule  *)
    do_under_baga_approx := flag;
    res
  with _ as e ->
    (do_under_baga_approx := flag;
     raise e)

let wrap_reverify_scc f a b c =
  let flag = !reverify_flag in
  reverify_flag := true;
  try
    let res = f a b c in
    (* restore flag do_classic_frame_rule  *)
    reverify_flag := flag;
    res
  with _ as e ->
    (reverify_flag := flag;
     raise e)

let wrap_norm flag norm f a =
  try
    let res = f a in
    if flag then norm res
    else res
  with _ as e ->
    raise e

let toggle_local obj f flag =
  if flag then (* infer_const_ *)obj # set f
  else (* infer_const_ *)obj # reset f

let toggle f flag = toggle_local infer_const_obj f flag
  (* if flag then infer_const_obj # set f *)
  (* else infer_const_obj # reset f *)

(* let wrap_pure_field et f a = *)
(*   let old_flag = infer_const_obj # get INF_PURE_FIELD  in *)
(*   let new_flag = (match et with *)
(*       | None -> infer_const_obj # get INF_PURE_FIELD  (\* !opt_classic *\) *)
(*       | Some b -> b) in *)
(*   if new_flag!=old_flag then toggle INF_PURE_FIELD new_flag; *)
(*   try *)
(*     let res = f a in *)
(*     (\* restore flag sa_pure_field *\) *)
(*     toggle INF_PURE_FIELD old_flag; *)
(*     res *)
(*   with _ as e -> *)
(*     (toggle INF_PURE_FIELD old_flag; *)
(*      raise e) *)

let wrap_gen_local obj attr et f a =
  let old_flag = obj (* infer_const_obj *) # get attr  in
  let new_flag = (match et with
      | None -> obj (* infer_const_obj *) # get attr  (* !opt_classic *)
      | Some b -> b) in
  if new_flag!=old_flag then toggle_local obj attr new_flag;
  try
    let res = f a in
    (* restore flag sa_pure_field *)
    toggle_local obj attr old_flag;
    res
  with _ as e ->
    (toggle_local obj attr old_flag;
     raise e)

let wrap_gen_global attr et f a = 
  wrap_gen_local Globals.infer_const_obj attr et f a 

let wrap_gen attr et f a = wrap_gen_local infer_const_obj attr et f a

let wrap_pure_field et f a = wrap_gen INF_PURE_FIELD et f a

(* let wrap_pure_field et f a = *)
(*   let flag = !Globals.sa_pure_field in *)
(*   sa_pure_field := (match et with *)
(*       | None -> infer_const_obj # get INF_PURE_FIELD  (\* !opt_classic *\) *)
(*       | Some b -> b); *)
(*   try *)
(*     let res = f a in *)
(*     (\* restore flag sa_pure_field *\) *)
(*     Globals.sa_pure_field := flag; *)
(*     res *)
(*   with _ as e -> *)
(*     (Globals.sa_pure_field := flag; *)
(*      raise e) *)

(* let wrap_classic et f a = *)
(*   let flag = !do_classic_frame_rule in *)
(*   do_classic_frame_rule := (match et with *)
(*       | None -> infer_const_obj # get INF_CLASSIC  (\* !opt_classic *\) *)
(*       | Some b -> b); *)
(*   try *)
(*     let res = f a in *)
(*     (\* restore flag do_classic_frame_rule  *\) *)
(*     do_classic_frame_rule := flag; *)
(*     res *)
(*   with _ as e -> *)
(*     (do_classic_frame_rule := flag; *)
(*      raise e) *)

let wrap_msg msg f a = 
  let () = y_binfo_pp ("====WRAP START " ^ msg) in
  try 
    let r = f a in
    let () = y_binfo_pp ("====WRAP END " ^ msg) in
    r
  with e ->
    let () = y_binfo_pp ("====WRAP END (exc) " ^ msg) in
    raise e

let wrap_classic str et f a = 
  let r = "wrap_gen" ^ str ^ ((pr_option string_of_bool) et) in
  if !Globals.new_trace_classic then wrap_msg r (wrap_gen INF_CLASSIC et f) a
  else (wrap_gen INF_CLASSIC et f) a

let wrap_classic_local obj et f a = wrap_gen_local obj INF_CLASSIC et f a

let wrap_ana_ni et f a = wrap_gen_global INF_ANA_NI et f a

    (* !do_classic_frame_rule *)

(* let set_classic f  = let () = x_binfo_pp "should use wrap_classic instead" no_pos in *)
(*                          () *)

(* Some f - set allow_field_imm t f *)
(* None - use the default option *)
let wrap_field_imm et f a =
  let flag = !allow_field_ann in
  let flag2 = !imm_merge in
  allow_field_ann := (match et with
      | None -> infer_const_obj # get INF_FIELD_IMM  (* !opt_classic *)
      | Some b -> b);
  if !allow_field_ann then imm_merge :=true;
  try
    let res = f a in
    allow_field_ann := flag;
    imm_merge := flag2;
    res
  with _ as e ->
    (allow_field_ann := flag;
     imm_merge := flag2;
     raise e)



(* let wrap_efa_exc et f a = *)
(*   let flag = !enable_error_as_exc in *)
(*   enable_error_as_exc := (match et with *)
(*       | None -> infer_const_obj # get INF_DE_EXC  (\* !opt_efa *\) *)
(*       | Some b -> b); *)
(*   try *)
(*     let res = f a in *)
(*     (\* restore flag enable_error_as_exc  *\) *)
(*     enable_error_as_exc := flag; *)
(*     res *)
(*   with _ as e -> *)
(*     (enable_error_as_exc := flag; *)
(*      raise e) *)

(* !!! **wrapper.ml#134:Calling wrap_err_pre *)
(* !!! **wrapper.ml#94:wrap_inf_obj:@dis_err *)
(* !!! **wrapper.ml#95:BEFORE:[] *)
(* !!! **wrapper.ml#98:AFTER:[@dis_err] *)
(* !!! **wrapper.ml#102:RESTORE:[] *)


(* !!! **wrapper.ml#134:Calling wrap_err_pre *)
(* !!! **wrapper.ml#94:wrap_inf_obj:@err_may *)
(* !!! **wrapper.ml#95:BEFORE:[@err_must] *)
(* !!! **wrapper.ml#98:AFTER:[@err_may,@err_must] *)
(* !!! **wrapper.ml#102:RESTORE:[@err_must] *)

let wrap_inf_obj iobj f a =
  let () = y_tinfo_hp (add_str "wrap_inf_obj" string_of_inf_const) iobj in
  let () = y_tinfo_hp (add_str "BEFORE" pr_id) infer_const_obj#string_of in
  let flag = not(infer_const_obj # get iobj) in
  let () = if flag then infer_const_obj # set iobj in
  let () = y_tinfo_hp (add_str "AFTER" pr_id) infer_const_obj#string_of in
  try
    let res = f a in
    if flag then infer_const_obj # reset iobj;
    (* let () = x_binfo_hp (add_str "RESTORE" pr_id) infer_const_obj#string_of no_pos in *)
    res
  with _ as e ->
    begin
      if flag then infer_const_obj # reset iobj;
      (* let () = x_binfo_hp (add_str "RESTORE" pr_id) infer_const_obj#string_of no_pos in *)
      raise e
    end

let wrap_inf_obj_lst lst f a =
  let rec aux lst f = match lst with
    | [] -> f a
    | i::lst -> aux lst (wrap_inf_obj i f)
  in aux lst f

let wrap_inf_obj_only io f a =
  let lst = io # get_lst in
  wrap_inf_obj_lst lst f a

let wrap_err_dis f a =
  wrap_inf_obj INF_DE_EXC f a

let wrap_err_may f a =
  wrap_inf_obj INF_ERR_MAY f a

let wrap_err_may f a =
  Debug.no_1 "wrap_err_may" pr_none pr_none (wrap_err_may f) a

let wrap_err_must f a =
  wrap_inf_obj INF_ERR_MUST f a

let wrap_err_bind f a =
  if infer_const_obj # is_dis_err then wrap_err_dis f a
  else if infer_const_obj # is_err_must then
    wrap_err_must f a
  else wrap_err_dis f a

let wrap_err_assert_assume f a =
  wrap_err_bind f a
(* if infer_const_obj # is_dis_err then wrap_err_dis f a *)
(* else wrap_err_must f a *)

(* not called? *)
let wrap_err_pre f a =
  (* let () = x_binfo_pp "Calling wrap_err_pre" no_pos in *)
  if infer_const_obj # is_dis_err then wrap_err_dis f a
  (* else if infer_const_obj # is_pre_must then wrap_err_must f a *)
  else if infer_const_obj # is_err_may then wrap_err_may f a
  else if infer_const_obj # is_err_must then wrap_err_may f a
  else  wrap_err_dis f a

let wrap_err_post f a =
  wrap_err_bind f a
(* if infer_const_obj # is_dis_err then wrap_err_dis f a *)
(* else wrap_err_must f a *)

let wrap_par_case_check f c =
  let flag = !ho_always_split in
  ho_always_split := true;
  try
    let res = f c in
    ho_always_split := flag;
    res
  with _ as e ->
    (ho_always_split := flag;
     raise e)
    (* 1 *)

let wrap_set_infer_type t f a =
  let flag = infer_const_obj # is_infer_type t in
  let () = Debug.ninfo_hprint (add_str "infer_type" string_of_inf_const) t no_pos in
  let () = Debug.ninfo_hprint (add_str "wrap set(old)" string_of_bool) flag no_pos in
  let () = infer_const_obj # set t in
  (* let flag2 = infer_const_obj # is_infer_type t in *)
  (* let () = x_binfo_hp (add_str "wrap set(new)" string_of_bool) flag2 no_pos in *)
  try
    let res = f a in
    (* restore flag do_classic_frame_rule  *)
    if not(flag) then infer_const_obj # reset t;
    res
  with _ as e ->
    (if not(flag) then infer_const_obj # reset t ;
     raise e)

let wrap_add_flow f a = wrap_set_infer_type INF_FLOW f a

let wrap_gen save_fn set_fn restore_fn flags f a =
  (* save old_value *)
  let old_values = save_fn flags in
  let () = set_fn flags in
  try 
    let res = f a in
    (* restore old_value *)
    let () = restore_fn old_values in
    res
  with _ as e ->
    (restore_fn old_values;
     raise e)

let wrap_ver_post f a = wrap_set_infer_type INF_VER_POST f a

(* let wrap_arr_as_var f a =  *)
(*   let () = x_binfo_pp "inside wrap_as_var" no_pos in  *)
(*   wrap_set_infer_type INF_ARR_AS_VAR f a *)

(* let wrap_arr_as_var f a =  *)
(*   Debug.no_1 "wrap_arr_as_var" pr_none pr_none (wrap_arr_as_var f) a *)

(* let wrap_ver_post f a = *)
(*   let save_fn () = infer_const_obj # is_ver_post in *)
(*   let set_fn () = infer_const_obj # set INF_VER_POST in *)
(*   let restore_fn f = if f then () else infer_const_obj # reset INF_VER_POST in *)
(*   wrap_gen save_fn set_fn restore_fn () f a *)

let wrap_one_bool flag new_value f a =
  let save_fn flag = (flag,!flag) in
  let set_fn flag = flag := new_value in
  let restore_fn (flag,old_value) = flag := old_value in
  wrap_gen save_fn set_fn restore_fn flag f a

let wrap_after code f a =
  try
    let r = f a in
    let () = code () in
    r
  with e ->
    let () = code () in
    raise e
   
let print_header s =
  print_endline_quiet "\n=====================================";
  print_endline_quiet ("   "^s);
  print_endline_quiet "====================================="

let wrap_lemma_quiet f a =
  wrap_one_bool Globals.lemma_ep_verbose false f a

let wrap_dd s f a =
  let s1 = "START -dd "^s in
  let s2 = "END   -dd "^s in
  let () = print_header s1 in
  wrap_after (fun () -> print_header s2) 
    (wrap_one_bool Debug.devel_debug_on true f) a

let wrap_two_bools flag1 flag2 new_value f a =
  let save_fn (flag1,flag2) = (flag1,flag2,!flag1,!flag2) in
  let set_fn (flag1,flag2) = (flag1 := new_value; flag2:=new_value) in
  let restore_fn (flag1,flag2,old1,old2) = flag1 := old1; flag2:=old2 in
  wrap_gen save_fn set_fn restore_fn (flag1,flag2) f a

let wrap_two_bools flag1 flag2 new_value f a =
  let pr r = string_of_bool !r in 
  Debug.no_2 "" pr pr (fun _ -> pr_pair pr pr (flag1,flag2)) (fun _ _ -> wrap_two_bools flag1 flag2 new_value f a) flag1 flag2 

(* let wrap_general flag new_value f a = *)
(*   (\* save old_value *\) *)
(*   let old_value = !flag in *)
(*   flag := new_value; *)
(*   try  *)
(*     let res = f a in *)
(*     (\* restore old_value *\) *)
(*     flag := old_value; *)
(*     res *)
(*   with _ as e -> *)
(*       (flag := old_value; *)
(*       raise e) *)

let wrap_no_filtering f a =
  wrap_one_bool filtering_flag false f a

let wrap_silence_output f a =
  wrap_one_bool Gen.silence_output true f a

let wrap_wo_int_to_imm f a =
  wrap_one_bool  Globals.int2imm_conv false f a

let wrap_with_int_to_imm f a =
  wrap_one_bool  Globals.int2imm_conv true f a

let wrap_dis_non_linear f a =
  wrap_two_bools  Globals.non_linear_flag Globals.filtering_flag false f a

(* let wrap_redlog_only f a = *)
(*   wrap_one_bool Redlog.dis_omega true f a *)

(* let wrap_oc_redlog f a = *)
(*   wrap_one_bool Redlog.dis_omega false f a *)

let wrap_lbl_dis_aggr f a =
  if !Globals.inv_wrap_flag
  then wrap_two_bools label_aggressive_sat label_aggressive_imply false f a
  else f a

let wrap_lemma_safe f a =
  wrap_one_bool Globals.check_coercions true f a

let wrap_lemma_unsafe f a =
  wrap_one_bool Globals.check_coercions false f a

(* let proof_no = ref 0 *)

(* let next_proof_no_str () = *)
(*   proof_no := !proof_no + 1; *)
(*   string_of_int !proof_no *)

(* let get_proof_no () = !proof_no *)

(* let sleek_proof_no = ref 0 *)

(* let last_sleek_fail_no = ref 0 *)

(* let get_sleek_no () = !sleek_proof_no *)

(* let get_last_sleek_fail () = !last_sleek_fail_no *)

(* let set_last_sleek_fail () =  *)
(*   last_sleek_fail_no := !sleek_proof_no *)

(* let next_sleek_int () : int = *)
(*   sleek_proof_no := !sleek_proof_no + 1;  *)
(*   (!sleek_proof_no) *)

let wrap_arr_as_var f a =
  let () = x_tinfo_pp "Calling wrap_arr_as_var" no_pos in
  let flag = !Globals.array_translate in
  Globals.array_translate := true;
  try
    let res = f a in
    Globals.array_translate := flag;
    res
  with _ as e ->
    (Globals.array_translate := flag;
     raise e)

let wrap_arr_as_var f a =
  Debug.no_1 "wrap_arr_as_var" pr_none pr_none (wrap_arr_as_var f) a

let wrap_pre_post_process f_pre f_post f a =
  let a = f_pre a in
  let res = f a in
  let res = f_post res in
  res

let wrap_z_debug f a b =
  let flag = !z_debug_flag in
  z_debug_flag := true;
  try
    let res = f a b in
    z_debug_flag := flag;
    res
  with _ as e ->
    (z_debug_flag := flag;
     raise e)
