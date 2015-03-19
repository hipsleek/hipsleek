int foo(int n)
 case {
  n>0 -> requires Term[] ensures res=n+1;
  n<=0 -> requires Term[] ensures res=n-1;
 }
{
  if(n>0)
  return n+1;
  else return n-1;
}

int fact(int x)
 infer [@term] requires true  ensures true;
/*
 case {
   x<0 -> requires Loop ensures false;
   x=0 -> requires Term[] ensures true;
   x>0 -> requires Term[x] ensures true;
 }
*/
//  requires true  ensures Uf(x,res);
//  requires true ensures res=x;
{
  if (x==0) return 1;
  else return foo(1) + fact(x - 1);
}
/*
# foo-fact2.ss

Good..

Termination Inference Result:
fact:  case {
  1<=x -> requires emp & Term[31,3,-1+(1*x)]
 ensures emp & true; 
  x<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  x=0 -> requires emp & Term[31,1]
 ensures emp & true; 
  }

*/
