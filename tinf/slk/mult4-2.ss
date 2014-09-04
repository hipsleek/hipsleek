bool nondet ()
  requires Term
  ensures true;
  
void f(int x,bool b)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    if (b) f(x - 1,b);
    else f(x + 1,b);
  }
}
  
/*
# mult4-2.ss

 our case-analysis don't work with boolean?

Expect one Loop and one Term..

GOT:
Termination Inference Result:
f:  case {
  0<=x & 1<=b -> requires emp & MayLoop[]
 ensures emp & true; 
  x<=(0-1) -> requires emp & Term[30,1]
 ensures emp & true; 
  b<=0 & 0<=x -> requires emp & MayLoop[]
 ensures emp & true; 
  }

*/
