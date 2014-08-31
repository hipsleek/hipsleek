UTPre@f fpre(int x).
UTPost@f fpost().

int fact(int x)
  infer [@term]
  requires true & fpre(x)
  ensures res>=1 & fpost(); //maybe just use TPost@f
  /*  
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires fpre(x) ensures fpost();
  }
  */
{
  if (x==0) return 1;
  else return 1+fact(x - 1);
}

/*
# fact2.ss

 Derived x-1 as ranking function;maybe can have a simplification which
 returns x instead?


Termination Inference Result:
f:  case {
  1<=x -> requires emp & Term[-1+(1*x)]
 ensures emp & true; 
  x<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  x=0 -> requires emp & Term[]
 ensures emp & true; 



*/
