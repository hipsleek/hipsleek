int foo1(int n)
  infer [@pre_n,@post_n]
  requires true ensures true;
{
  if (n == 0) return 0;
  else return 1+foo2(n-1);
}

int foo2(int n)
  infer [@pre_n,@post_n]
  requires true ensures true;
{
  if (n == 0) return 0;
  else return 1+foo1(n-1);
}

/*

Why don't have pre rel

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1193(n,res), ((n=res & 1<=res) | (res=0 & n<=0)), true, true),
( post_1194(n,res), ((n=res & 1<=res) | (res=0 & n<=0)), true, true)]
*************************************

!!! REL POST :  post_1194(n,res)
!!! POST:  ((n=res & 1<=res) | (res=0 & n<=0))
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  post_1193(n,res)
!!! POST:  ((n=res & 1<=res) | (res=0 & n<=0))
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
foo1$int
 requires emp & MayLoop[]
     ensures emp & ((n=res & 1<=res) | (res=0 & n<=0));

Post Inference result:
foo2$int
 requires emp & MayLoop[]
     ensures emp & ((n=res & 1<=res) | (res=0 & n<=0));

*/
