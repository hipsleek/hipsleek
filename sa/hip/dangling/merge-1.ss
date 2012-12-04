/* merge sort */

data node {
	int val; 
	node next; 
}

HeapPred H(node a). 
HeapPred G(node a,node b). 

/* function to insert an element in a sorted list */
node insert(node x, int v)
  infer [H,G]
  requires H(x)
  ensures G(x,res);
{
	node tmp;	

	if (v <= x.val)
		return new node(v, x);
	else
	{
		if (x.next != null)
		{
			x.next = insert(x.next, v);
      return x;
		}
		else
    {
			x.next = new node(v,null);
      return x;
    }
	}
}

/*
 H(x) ::= x::node<_,n> * HP(n)
   HP(x) ::= x=null
    or HP2(x)
    or x::node<_,nn>*HP(x)

   G(x) ::= x::node<_,n> * n::node<_,q> * HP3(q)
   HP3(x) ::= x=null
    or HP2(x)
    or x::node<_,nn>*HP3(x)
 */
