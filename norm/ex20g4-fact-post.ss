

HeapPred P(int x).

relation R(int x).
  relation R2(int x,int y).

int fact(int i)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
//infer [P,@classic,@pure_field]
//  requires P(i)
  infer [R2]
  requires true
  ensures  R2(i,res);
{    
  if (i==0) return 1;
  else return i + fact(i-1);
}

/*
# ex20g4.ss 

  infer [R2]
  requires true
  ensures  R2(i,res);
{    
  if (i==0) return 1;
  else return i + fact(i-1);
}

!!! **fixcalc.ml#1046:Input of fixcalc: :R2:={[i] -> [res] -> []: (i=0 && res=1 ||  (exists (v_int_19_1684: (exists (v_int_19_1682:v_int_19_1682+1=i && R2(v_int_19_1682,v_int_19_1684)))  && v_int_19_1684+i=res))  && ((i<0) || (i>0)))
};
bottomupgen([R2], [2], SimHeur);
!!! **fixcalc.ml#393:svls (orig):[[R2:RelT([]),res:int,i:int]]
!!! **fixcalc.ml#394:svl1 (from parse_fix):[[res:int,i:int]]
!!! **fixcalc.ml#395:svl2 (from parse_fix):[[res:int,i:int]]
!!! **fixcalc.ml#1074:Result of fixcalc (parsed): :[ i>=0 & res>=(1+i)]
!!! **pi.ml#754:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#755:>>REL POST:  R2(i,res)
!!! **pi.ml#756:>>POST:  i>=0 & res>=(1+i)

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
