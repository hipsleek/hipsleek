
void main(ref int x, ref int y)
  infer[@post_n]
  requires true  ensures true; 
{
  while (y<x) 
    infer[@post_n]
  requires true  ensures true; 
  {
    y++;
  }
}
/*
 requires emp & MayLoop[]
     ensures emp & x'=x & (((y'=x & y<x) | (y'=y & 
x<=y)));

main$int~int
 requires emp & MayLoop[]
     ensures emp & x'=x & (((y'=x & y<x) | (y'=y & 
x<=y)));

*/
