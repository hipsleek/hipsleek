class Exp extends __Exc {
  int val;
}

void loop(ref int x)
  infer [@post_n]
  requires true
  ensures  true & flow __norm;
{
  if (x>0) {
    /* raise new Exp(2); */
    x = x-1;
    loop(x);
  } else {
    return;
  }
}

/*
# flow2a.ss

[( post_1210(x,x'), ((x'=0 & 1<=x) | (x'=x & x<=0)), true, true)]
*************************************

!!! REL POST :  post_1210(x,x')
!!! POST:  ((x'=0 & 1<=x) | (x'=x & x<=0))
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
loop$int
 requires emp & MayLoop[]
     ensures emp & ((x'=0 & 1<=x) | (x'=x & x<=0));

*/
