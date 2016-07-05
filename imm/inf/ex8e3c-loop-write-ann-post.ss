data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P1]
  requires c::cell<v>@M 
  ensures c::cell<w>@b & P1(b) ;
{
 int x = c.fst;
 if (x!=1) {
   c.fst =c.fst-1;
   int tmp=2+foo(c);
   dprint;
   return tmp;
 } else return 0;
}

/*
# ex8e3c.ss --trace-exc

# fixcalc format error

!! **fixcalc.ml#160:fixcalc trans error :: b_1519<:b_1465Exception(fixcalc_of_pure_formula(really called)):Globals.Illegal_Prover_Format("Fixcalc.fixcalc_of_b_formula: Do not support bag, list")
Exception(fixcalc_of_pure_formula):Globals.Illegal_Prover_Format("Fixcalc.fixcalc_of_b_formula: Do not support bag, list")
Exception(compute_def):Failure("compute_def:Error in translating the input for fixcalc")
Exception(compute_fixpoint_aux):Failure("compute_def:Error in translating the input for fixcalc")
Exception(compute_fixpoint):Failure("compute_def:Error in translating the input for fixcalc")
ExceptionFailure("compute_def:Error in translating the input for fixcalc")Occurred!
Exception occurred: Failure("compute_def:Error in translating the input for fixcalc")


*/
