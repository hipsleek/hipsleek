void f(int x, int y)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    f(x - y, y);
    f(x + y, y);
  }
}
/*
# mult4b.ss

f:  case {
  0<=x -> case {
           y<=0 -> requires emp & Loop[]
 ensures false & false; 
           1<=y -> requires emp & Loop[]
 ensures false & false; 
           }
  
  x<=(0-1) -> requires emp & Term[30,1]
 ensures emp & true; 
  }
*/

