/* merge sort */

data node {
	int val; 
	node next; 
}

bool rand()
 requires true
 ensures !res or res;

HeapPred H(node a). 
HeapPred G(node a,node b). 

/* function to insert an element in a sorted list */
node insert(node x, int v)
  infer [H,G]
  requires H(x)
  ensures G(x,res);
{
	node tmp;	

    int r = x.val;
	if (rand())
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
