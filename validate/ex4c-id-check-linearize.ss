data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void foo(node x)
  requires x::node<aaa,q>*q::node<aaa,null> 
  ensures x::ll<n>;
