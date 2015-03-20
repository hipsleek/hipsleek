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

let wrap_exception dval f e =
  try
    f e
  with _ -> dval

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

let wrap_classic et f a =
  let flag = !do_classic_frame_rule in
  do_classic_frame_rule := (match et with
    | None -> infer_const_obj # get INF_CLASSIC  (* !opt_classic *)
    | Some b -> b);
  try
    let res = f a in
    (* restore flag do_classic_frame_rule  *)
    do_classic_frame_rule := flag;
    res
  with _ as e ->
    (do_classic_frame_rule := flag;
    raise e)

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
1
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

let wrap_redlog_only f a =
  wrap_one_bool Redlog.dis_omega true f a

let wrap_oc_redlog f a =
  wrap_one_bool Redlog.dis_omega false f a

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
