bool nondet ()
  requires Term
  ensures true;
  
void f(int x,int b)
  infer [@term]
  requires true ensures true;
{
  if (x < 0) return;
  else {
    if (b>1) f(x - 1,b);
    else f(x + 1,b);
  }
}
  
/*
# mult4-2a.ss

EXPECT:
  case{
   x>=0 -> 
     case {
      b>1 -> Term[x]
      b<=1 -> Loop ..
   x<0 -> Term[]

GOT:
f:  case {
  0<=x -> requires emp & MayLoop[]
 ensures emp & true; 
  x<=(0-1) -> requires emp & Term[31,1]
 ensures emp & true; 
  }


*/
