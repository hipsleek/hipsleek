
data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
	inv n >= 0;

/*
int id(int x)
  requires x+3+2 <2 
  ensures 0<res;
{    
  return x;
}
*/

node id(node x)
  requires x::ll<nn> & x!=null
  ensures res::ll<nn> & nn>0;
{    
  return x;
}

/*
node id2(node y)
  requires true //y::ll<b> & y!=null
  ensures res::ll<zz> & zz>0;
{    
  return y;
}
*/
