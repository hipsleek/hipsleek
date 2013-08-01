/* insertion sort */

data node {
	int val; 
	node next; 
}


bnd<n, sm, bg> == self = null & n = 0 or 
                  self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d < bg
               inv n >= 0;


sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or 
                  self::node<sm, q> * q::sll<n-1, qs, lg> & q != null & sm <= qs
               inv n >= 1 & sm <= lg;

ll0<> == self = null
	or self::node<_, q> * q::ll0<> 
  inv true;

HeapPred H1(node a).
HeapPred H2(node a).
/* function to insert an element in a sorted list */
node insert(node x, int v)
  /* requires x::sll<n, xs, xl> & n > 0  */
  /* ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres = max(v,xl); */
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

HeapPred H3(node a).
HeapPred H4(node a).
HeapPred H5(node a).
/* insertion sort */
void insertion_sort(node x, ref node y)
	/* requires x::ll0<>* y::ll0<> */
    /* ensures y'::ll0<> ; //' */
  infer[H3,H4,H5]
  requires H3(x)*H5(y)
  ensures H4(y');//'
{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}














































