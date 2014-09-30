// this is expected outcome from inferring t5-i.ss

data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

int hd(node x)
 requires x::ll<n> & x!=null
  ensures x::node<res,q>*q::ll<n-1>; 
{
  return x.val;
}

node tl(node x)
  requires x::node<_,q>@L
  ensures res=q;
{
  return x.next;
}


// Fail
int hdtl(ref node x)
  requires x::node<a,q> * q::node<b,z> * z::ll<n>
  ensures x::node<a,q> * q::node<_,z1> * z1::ll<n> & x'=q ;//'
{
  x = tl(x);
  int h = hd(x);
  //dprint;
  return h;
}

