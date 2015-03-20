#include "xdebug.cppo"
module CP = Cpure

let pr_sv = CP.string_of_spec_var
let pr_svl = CP.string_of_spec_var_list

let stk_vars = new Gen.stack_pr (pr_sv) CP.eq_spec_var_nop

let stk_evars = new Gen.stack_pr (pr_sv) CP.eq_spec_var_nop

let in_vars = new VarGen.store [] pr_svl
