data node {
  int val;
  node next;
}


llf<v,n> == self = null & n = 0 
  or self::node<v, q> * q::llf<_,n-1> 
  inv n >= 0;

int hd(node x)
  infer [n] 
  requires x::llf<v,n>
  ensures true; //'
/*
   expecting
   requires x::llf<v,n> & n>0
   ensures  x::llf<v,n> & res=v 
*/
{
  return x.val;
}
