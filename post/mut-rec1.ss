relation Uf1(int n, int r).
  relation Uf2(int n, int r).

/*
  int foo1(int n)
infer[Uf1]
requires true
  ensures Uf1(n,res);
{
  if (n <= 0) return 0;
  else return 1+foo1(n-1);
}

  int foo2(int n)
infer[Uf2]
requires true
  ensures Uf2(n,res);
{
  if (n <= 0) return 0;
  else return 1+foo2(n-1);
}
*/

int foo1(int n)
  infer[Uf1,Uf2]
  requires true
  ensures Uf1(n,res);
{
  if (n <= 0) return 0;
  else return 1+foo2(n-1);
}

int foo2(int n)
  infer[Uf1,Uf2]
  requires true
  ensures Uf2(n,res);
{
  if (n <= 0) return 0;
  else return 1+foo1(n-1);
}

/*
# mut-rec1.ss

Please look at examples of mutual-recursive fixpoint
in fixcalc. Please see how to invoke those commands.

Please add aux-recursion as well to your example

Checking procedure foo2$int... 
!!! WARNING : Inferable vars include some external variables!
vars:[Uf1,Uf2] pre_post_vars:[Uf2,res,n]

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN Uf1: ( res=0 & n<=0) -->  Uf1(n,res),
RELDEFN Uf1: ( Uf2(v_int_30_1193,v_int_30_1197) & 0<=v_int_30_1193 & v_int_30_1197=res-1 & 
n=v_int_30_1193+1) -->  Uf1(n,res),
RELDEFN Uf2: ( res=0 & n<=0) -->  Uf2(n,res),
RELDEFN Uf2: ( Uf1(v_int_39_1229,v_int_39_1236) & 0<=v_int_39_1229 & v_int_39_1236=res-1 & 
n=v_int_39_1229+1) -->  Uf2(n,res)]
*************************************

!!! PROBLEM with fix-point calculation
Procedure foo2$int FAIL.(2)

 */
