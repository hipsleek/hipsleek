

HeapPred P(int x).

relation R(int x).

int fact(int i)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
//infer [P,@classic,@pure_field]
//  requires P(i)
/*
  infer [R]
  requires R(i)
  ensures false;
*/
  requires i<(0)
  ensures false;
{    
  if (i==0) return 1;
  else return i * fact(i-1);
}

/*
# ex20g2.ss 

int fact(int i)
  infer [R]
  requires R(i)
  ensures false;
{    
  if (i==0) return 1;
  else return i * fact(i-1);
}

*************************************
******pure relation assumption 1 *******
*************************************
[RELDEFN R: ( R(i) & i=1+v_int_18_1500' & (v_int_18_1500'+1)!=0) -->  R(v_int_18_1500'),
RELASS [R]: ( R(i)) -->  i!=0]


!!! PROBLEM with fix-point calculation
ExceptionFailure("substitute_args: failure with look_up_rel_args_type")Occurred!

Error1(s) detected at main 
Stop z3... 66 invocations 
Stop Omega... 18 invocations caught

Exception occurred: Failure("substitute_args: failure with look_up_rel_args_type")
Error3(s) detected at main 


*/
