/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
cll<p, n> == self = p & n = 0
	or self::node<_, r> * r::cll<p, n-1> & self != p  
	inv n >= 0;

hd<n> == self = null & n = 0
	or self::node<_, r> * r::cll<self, n-1>  
	inv n >= 0;


relation A(int x, int y).


/* functions to count the number of nodes in a circular list */
int count(node x, node h)
    infer [A]
    requires x::cll<p, n> & h=p
    ensures x::cll<p, n> & A(res,n); //res=n; 

{
	int n;
	
	if (x == h){
    dprint;
		return 0; 
  }
	else
	{
    //assume false;
		n = count(x.next, h);
		n = n + 1;
    dprint;
		return n;
	}
}

