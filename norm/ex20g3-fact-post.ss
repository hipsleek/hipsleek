

HeapPred P(int x).

relation R(int x).

int fact(int i)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
//infer [P,@classic,@pure_field]
//  requires P(i)
  infer [R]
  requires true
  ensures  R(i);
{    
  if (i==0) return 1;
  else return i * fact(i-1);
}

/*
# ex20g3.ss 

  infer [R]
  requires true
  ensures  R(i);
{    
  if (i==0) return 1;
  else return i * fact(i-1);
}

*************************************
****** Before putting into fixcalc*******
pre_vars: i
post_vars: 
*************************************
formula:  (i=0 | 
  exists(v_int_18_1526:exists(i':exists(v_int_18_1528:exists(v_int_18_1503':
                                 exists(res:res=v_int_18_1503') & 
                                 v_int_18_1503'=i'*v_int_18_1528)) & 
                                 1+v_int_18_1526=i' & i'=i & i'!=0) & 
                       R(v_int_18_1526)))
*************************************

# error below caused by *. Need a process to weaken
  multiplication before passing to fixcalc:
  (r=a*b) ==> (a=0 | b=0) -> r=0
       & (a=1 -> r=b)
       & (b=1 -> r=a)

# it may be useful to  have more general property:
  (r=a*b) ==> (a>=0 & b>=0 | a<=0 & b<=0->r>=0
    &  (a<0 & b>0 | a>0 & b<0) -> r<0

ERROR: at _0:0_0:0
Message: compute_def:Error in translating the input for fixcalc>>fromGlobals.Illegal_Prover_Format("Fixcalc.fixcalc_of_exp: Not supported expression")
Exception(compute_def):Failure("compute_def:Error in translating the input for fixcalc>>fromGlobals.Illegal_Prover_Format(\"Fixcalc.fixcalc_of_exp: Not supported expression\")")
Exception(compute_fixpoint_aux):Failure("compute_def:Error in translating the input for fixcalc>>fromGlobals.Illegal_Prover_Format(\"Fixcalc.fixcalc_of_exp: Not supported expression\")")
Exception(compute_fixpoint_aux):Failure("compute_def:Error in translating the input for fixcalc>>fromGlobals.Illegal_Prover_Format(\"Fixcalc.fixcalc_of_exp: Not supported expression\")")
Exception(compute_fixpoint_xx):Failure("compute_def:Error in translating the input for fixcalc>>fromGlobals.Illegal_Prover_Format(\"Fixcalc.fixcalc_of_exp: Not supported expression\")")
Exception(compute_fixpoint_x2):Failure("compute_def:Error in translating the input for fixcalc>>fromGlobals.Illegal_Prover_Format(\"Fixcalc.fixcalc_of_exp: Not supported expression\")")
Exception(compute_fixpoint_2):Failure("compute_def:Error in translating the input for fixcalc>>fromGlobals.Illegal_Prover_Format(\"Fixcalc.fixcalc_of_exp: Not supported expression\")")




*/
