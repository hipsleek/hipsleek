//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int a,int b).
  relation Q(int a,int b,int c,int r, int q).

  int foo(ref int a_5, ref int a_4)
  infer [P,Q] requires P(a_4,a_5) ensures Q(a_4,a_4',a_5,a_5',res);
{
  a_5=10;
  return a_4;
}

/*
# ex11d.ss 

infer [@arrvar,P,Q,update_array_1d] requires P(a) ensures Q(a,a',res);

# why is there exception despite @arrvar?

!!! **omega.ml#673:WARNING: exception from Omega.is_valid
!!! **omega.ml#673:WARNING: exception from Omega.is_valid

# need to fix fixcalc


Correct RElDEFN:
[RELDEFN Q: ( a'[4]=res & update_array_1d(a,a',10,5) & P(a)) 
     -->  Q(a,a',res)]

# However, it seems we cannot handle update_array_Id subsequently..

ERROR: at _0:0_0:0
Message: compute_def:Error in translating the input for fixcalc
!!! PROBLEM with fix-point calculation
ExceptionFailure("compute_def:Error in translating the input for fixcalc")Occurred!
Error1(s) detected at main 
Stop Omega... 46 invocations caught


[RELDEFN Q: ( 
a'[4]=res & update_array_1d(a,a',10,5) & P(a)) -->  Q(a,a',res)


// unchanged(a,a',fun i->i!=5)


a'[4]=res & a'[5]=10 & forall(i!=5->a'[i]=a[i]) & P(a) 
    -->  Q(a,a',res)

a'[4]=res & a'[5]=10 & P(a) & a'[4]=a[4]
    -->  Q(a,a',res)

[RELDEFN Q: 
 ( a_5'=10 & res=a_4' & a_4'=a_4 & P(a_4,a_5)) 
    -->  Q(a_4,a_4',a_5,a_5',res)]

a[4],a[5];a'[4],a'[5]


[RELDEFN Q: ( a_5'=10 & a_4=res & P(a_4,a_5)) -->  Q(a_4,a_5,a_5',res)]

// forall(i:i!=5->a'[i]=a[i])


*/
