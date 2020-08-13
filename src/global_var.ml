#include "xdebug.cppo"
module CP = Cpure

let pr_sv = CP.string_of_spec_var
let pr_svl = CP.string_of_spec_var_list
let pr_pair_id = fun (x,y) -> x ^ "-->" ^  y
let eq_pair_id = fun (x1,y1) (x2,y2) -> (x1=x2) && (y1=y2)

let stk_vars = new Gen.stack_pr "stk-vars" (pr_sv) CP.eq_spec_var_nop

let set_stk_vars vs =
  let () = stk_vars # reset in
  stk_vars # push_list vs

let stk_renamed_vars = new Gen.stack_pr "stk-renamed-vars" pr_pair_id eq_pair_id

let stk_evars = new Gen.stack_pr "stk-evars" (pr_sv) CP.eq_spec_var_nop

let stk_var_ident = new Gen.stack_pr "stk-var-ident" (Gen.pr_id) (=)

let in_vars = new VarGen.store [] pr_svl

let sleek_cnt_timeout_limit = new Gen.counter 5
