data node {
	int val; 
	node next;	
}

int sqrt(int n)
 case {
  n>=0 -> ensures res*res<n & (res-1)*(res-1) >=n
  n<0 -> ensures true & flow __Error
}


int node_sqrt1(node x)
  requires x::node<v,null> & v>=0
  ensures x::node<v,null> & v>=0 & res*res<n & (res-1)*(res-1) >=n;
/*
case
{
x = null -> ensures true & flow __Error;
x != null ->
//should be (extend case for heap)
//x::node<v,null>
  requires x::node<v,null>
case {
  v>= 0 -> ensures x::node<v,null> & v>=0 & res*res<n & (res-1)*(res-1) >=n;
  v<0 -> ensures  true & flow __Error;
}
*/
{
  if (x==null)
    return ierror();
  else
    if (x.val < 0)
      return ierror();
    else
      return sqrt(x.val);
}
