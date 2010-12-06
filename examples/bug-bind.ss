data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

// bug triggered by presence of global

global int a;



int foo22(node x)
	requires x::ll<n> & n>3
	ensures true;
{

  node x2=x.next;
  node x3 = x.next;
  int z;
  {
    int z;
    z=z+1;
    int z;
  bind x2 to (v,n) in { z= v; } 
  return z;
  }
}

