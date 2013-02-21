/* quick sort */

data node {
	int val; 
	node next; 
}

ll0<> == self = null
	or self::node<_, q> * q::ll0<> 
  inv true;

HeapPred H1(node a).
  HeapPred H2(node a,node b).

node partition(ref node xs, int c)
  /* requires xs::bnd<n, sm, bg> & sm <= c <= bg */
  /* ensures xs'::bnd<a, sm, c> * res::bnd<b, c, bg> & n = a+b; */
  /* requires xs::ll0<> */
  /* ensures xs'::ll0<> * res::ll0<>;//' */
  infer[H1,H2]
  requires H1(xs)
  ensures H2(xs',res);//'
{
	node tmp1;
	int v; 

	if (xs == null)
		return null;
	else
	{
		if (xs.val >= c)
		{
            v = xs.val;
			bind xs to (xsval, xsnext) in {
				tmp1 = partition(xsnext, c);
            }
			xs = xs.next;
			return new node(v, tmp1);
		}
		else {
          bind xs to (xsval, xsnext) in {
            tmp1 = partition(xsnext, c);
          }
          return tmp1;
		}
	}
}
