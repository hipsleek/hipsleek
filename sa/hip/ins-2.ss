data node {
	int val; 
	node next; 
}

ll0<> == self = null
	or self::node<_, q> * q::ll0<> 
  inv true;

HeapPred H1(node a).
HeapPred H2(node a).
/* function to insert an element in a sorted list */
node insert(node x, int v)
  /* requires x::ll0<> & x!=null */
  /* ensures res::node<_,p>*p::ll0<> & p !=null; */
  infer[H1,H2]
  requires H1(x)
  ensures H2(res);

{
        node tmp_null = null;
        node xn;

   if (v <= x.val) {
		return new node(v, x);
        }
	else {
      // assume false;
		if (x.next != null)
		{
                        xn = insert(x.next, v);
			x.next = xn;
			return x;
		}
		else
		{
			x.next = new node(v, tmp_null);
			return x;
		}
    }
}

void insertion_sort(node x, ref node y)
	requires x::ll0<>* y::ll0<>
    ensures y'::ll0<> ; //'
{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}
