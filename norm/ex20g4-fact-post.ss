

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
  else return i + fact(i-1);
}

/*
# ex20g4.ss 

  infer [R]
  requires true
  ensures  R(i);
{    
  if (i==0) return 1;
  else return i + fact(i-1);
}

# can we add i>=0 to pre-condition?
  How to use outcome of topdown?
  Has top-down been generalized to mutual recursion?

*************************************
****** Before putting into fixcalc*******
pre_vars: i
post_vars: 
*************************************
formula:  (i=0 | (exists(v_int_18_1526:v_int_18_1526+1=i & R(v_int_18_1526)) & i!=0))
*************************************

!!! **fixcalc.ml#1043:Input of fixcalc: :R:={[i] -> [] -> []: (i=0 ||  (exists (v_int_18_1526:v_int_18_1526+1=i && R(v_int_18_1526)))  && ((i<0) || (i>0)))
};
bottomupgen([R], [2], SimHeur);

===================
R:={[i] -> [] -> []: (i=0 ||  (exists (v_int_18_1526:v_int_18_1526+1=i && R(v_int_18_1526)))  && ((i<0) || (i>0)))
};
bottomupgen([R], [2], SimHeur);
# i>=0
topdown(R, 2, SimHeur);
# {[i,RECi]:((i >= RECi + 1 && 0 >= 1 + i) || (RECi >= 0 && i >= 1 + RECi))};


*/
