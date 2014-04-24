data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

int hd2(node x)
 infer [x] 
 requires x::ll<n>
 ensures true; //'
/*
   requires x::ll<n> & x!=null
   ensures x::ll<n> 
*/
{
  return x.val;
}

