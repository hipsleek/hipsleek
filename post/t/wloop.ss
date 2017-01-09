
void main(ref int x, ref int y)
  infer[@post_n,@term]
  requires true
  ensures true; 
{
  while (y<x) 
    infer[@post_n,@term]
  requires true
  ensures true; 
  {
    y++;
  }
}
/*
 requires emp & MayLoop[]
     ensures emp & x'=x & (((y'=x & y<x) | (y'=y & 
x<=y)));

# wloop.ss

  while (y<x) 
  infer[@post_n,@term]
  requires true
  ensures true; 
  {
    y++;
  }

Termination Inference Result:
while_7_2:  case {
  x<=y -> requires emp & Term[74,1]
     ensures emp & ((x=y' & y<y') | 
  (y=y' & x<=y')); 
  y<x -> requires emp & Term[74,2,-1+(1*x)+(-1*
  y)]
     ensures emp & ((x=y' & y<y') | (y=y' & x<=y')); 
  }

# Desired # can we combine the base and recursive case?

*/
