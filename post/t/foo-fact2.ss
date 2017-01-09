
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
  infer [@term
         ,@post
  ]
  requires true  ensures true;
{
  if (x==0) return 1;
  else return foo(1) + fact(x - 1);
}
/*
# foo-fact2.ss

Since both @term and @post are specified; we should
stage it by inferring @post first.
After that, we would infer @term:

We expect:
 Post Inference result:
 fact:
  requires true 
  ensures res=1+2*x & x>=0;

Then:
 Termination Inference Result:
 fact:  

fact:  case {
  1<=x -> requires emp & Term[31,3,-1+(1*x)]
 ensures emp & res=1+2*x & x>=0; 
  x<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  x=0 -> requires emp & Term[31,1]
 ensures emp & res=1+2*x & x>=0; 
  }

*/
