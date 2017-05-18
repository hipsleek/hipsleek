/*data node {
  // can we annotate fields?
  int val;
  node next;
}*/

pred_prim sec<i : int>;

global int i; // can we annotate i to say it's L or H?

global Flow;

int plus(int i, int j)
 requires true
 ensures Flow' = {i<:res, j<:res} union Flow;

int incr(int j)
  requires j <: L
  ensures res <: L;
{
  return plus(j,1);
}

int main(int b)
  requires true
  ensures true;
{
  int k = incr(i);
}
