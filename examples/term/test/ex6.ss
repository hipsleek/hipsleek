data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
	inv n >= 0;

node app2(node x, node y)
 requires x::ll<n> * y::ll<m> & n>=0
 variance (1) [len(x)]
 ensures res::ll<n+m>;
{
 if (x==null) return y;
 else {
   node w = x.next;
   //assert len(x)-len(w)>0;
   return new node(x.val,app2(x.next,y));
 }
}
