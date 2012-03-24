module CP = Cpure

let stk_vars = new Gen.stack_pr (!CP.print_sv) CP.eq_spec_var_nop

let stk_evars = new Gen.stack_pr (!CP.print_sv) CP.eq_spec_var_nop

let in_vars = new Globals.store [] !CP.print_svl
