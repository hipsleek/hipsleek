data node {
        int val;
        node next;
}

//p2<y> == self = y
//	or  y::node<_,t> * self::p2<t>  & self != y
//	inv true;

//infer
p2<x> == self = x
	or self::node<_,q> * q::p2<x> & self != x
	inv true;

p<> == self::node<_,t> * t::p2<self> 
	inv true;

//x is cll => x.next is cll ?

void ex41 (ref node x, node h)
// Ex 4.1
//temp spec
requires x::node<_,t> * t::p2<h> & h = x 
ensures x::node<_,t> * t::p2<h>  & x' = y;//'  
{
  node y = x;
  x = x.next;
dprint;
  while (x!=y) 
	requires x::node<_,t> * t::p2<h> 
	ensures x::node<_,t> * t::p2<h>& x' = y;//' 
	{	
		x = x.next;
	 } 

}


