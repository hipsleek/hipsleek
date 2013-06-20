data node {
  int val;
  node_star next;
}

data node_star {
  node pdata;
}

ll<n> == self = null & n = 0 
  or self::node_star<p> * p::node<_,q> * q::ll<n1> & n = n1 + 1
  inv n >= 0;

void foo(node x)
  requires x::node<_,_>
  ensures x::node<1,_>;
{
  x.val = 1;
}
