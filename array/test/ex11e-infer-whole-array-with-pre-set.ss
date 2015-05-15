//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
relation Q(int[] a,int[] b,int r).

int foo(ref int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
//  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
  infer [@arrvar,P,Q,update_array_1d] requires P(a) ensures Q(a,a',res);
// requires true ensures update(a,a',10,5) & res=a[4];
// requires true ensures a'[5]=10 & res=a[4];
{
  if (a[5]>4) {
    a[5]=10;
    return a[4];
  } else {//assume false;
      return -3;
  }
}

/*
The simplify is wrong...
(==tpdispatcher.ml#1928==)
Omega.simplify@13
Omega.simplify inp1 : ((exists(res:exists(a':a'[4]=res & a'[5]=10 & forall(i:(!(i!=5) | 
a'[i]=a[i])))) & 5<=(a[5])) | (exists(res:res=0-3) & exists(a':a'=a & 
(a'[5])<=4)))
Omega.simplify@13 EXIT: (5<=(a[5]) | a=a')

((exists(res:exists(a':a'[4]=res & a'[5]=10 & forall(i:(!(i!=5) |
a'[i]=a[i])))) & 5<=(a[5])) | (exists(res:res=0-3) & exists(a':a'=a &
(a'[5])<=4)))

This is wrong!!!!
But what is the meaning of such free var???

process_exists_array@62@61@60@59
process_exists_array inp1 : ((exists(res:exists(a':a'[4]=res & a'[5]=10 & forall(i:(!(i!=5) |
a'[i]=a[i])))) & 5<=(a[5])) | (exists(res:res=0-3) & exists(a':a'=a &
(a'[5])<=4)))
process_exists_array@62 EXIT: ((exists(res:exists(a___i___':exists(a___5___':exists(a___4___':a'[4]=res &
a'[5]=10 & forall(i:(!(i!=5) | a'[i]=a[i])))))) & 5<=(a[5])) |
(exists(res:res=0-3) & exists(a___5___':a'=a & (a'[5])<=4)))



# ex11d.ss 

int foo(ref int[] a)
  infer [@arrvar,P,Q,update_array_1d] requires P(a) ensures Q(a,a',res);
{
  a[5]=10;
  return a[4];
}


[RELDEFN Q: ( a'[4]=res & 5<=(a[5]) & update_array_1d(a,a',10,5) & P(a)) -->  Q(a,a',res),
RELDEFN Q: (  res=0-3 & a'=a & (a'[5])<=4 & P(a)) -->  Q(a,a',res)]

# @arrvar to be applied from here..


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

exist index ( a[index] index>1)

exist index ( a-index...)
*/
