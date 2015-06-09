//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
relation Q(int[] a,int[] b,int r).
  relation R(int a,int b).
int foo(ref int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
//  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
  infer [P,Q] requires P(a) ensures Q(a,a',res);
// requires true ensures update(a,a',10,5) & res=a[4];
// requires true ensures a'[5]=10 & res=a[4];
{
  if (a[5]>4) {
    a[5]=10;
    return a[4];
  } else {assume false;
      return -3;
  }
}

/*
# ex11e1.ss 

int foo(ref int[] a)
  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
{
  if (a[5]>4) {
    a[5]=10;
    return a[4];
  } else {assume false;
      return -3;
  }
}

*************************************
******pure relation assumption*******
*************************************
[RELDEFN Q: ( a'[4]=res & a'[5]=10 & forall(i:(!(i!=5) | a'[i]=a[i])) & 5<=(a[5]) & P(a)) -->  Q(a,a',res)]
*************************************

!!! **pi.ml#650:>>REL POST :  Q(a,a',res)
!!! **pi.ml#651:>>POST:  a'[4]=res & a'[5]=10 & forall(i:(!(i!=5) | a'[i]=a[i])) & 5<=(a[5])
!!! **pi.ml#652:>>REL PRE :  P(a)
!!! **pi.ml#653:>>PRE :  exists(a':a'[5]=10 & forall(i:(i=5 | a'[i]=a[i]))) & 5<=(a[5])

*/
