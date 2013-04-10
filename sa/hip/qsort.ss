/* quick sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or 
      self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d < bg 
      inv n >= 0;

sll<n, sm, lg> == 
     self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 
  or self::node<sm, q> * q::sll<n-1, qs, lg> &  sm <= qs 
      inv n >= 1 & sm <= lg & self!=null ;

ll0<> == self = null
	or self::node<_, q> * q::ll0<> 
  inv true;

HeapPred H1(node a).
  HeapPred H2(node a).
 HeapPred H3(node a).
node partition(ref node xs, int c)
  /* requires xs::bnd<n, sm, bg> & sm <= c <= bg */
  /* ensures xs'::bnd<a, sm, c> * res::bnd<b, c, bg> & n = a+b; */
  /* requires xs::ll0<> */
  /* ensures xs'::ll0<> * res::ll0<>;//' */
  infer[H1,H2,H3]
  requires H1(xs)
  ensures H2(xs')*H3(res);//'
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

HeapPred H4(node a).
HeapPred H5(node a).
HeapPred H7(node a).
HeapPred H6(node b, node c).

/* function to append 2 bounded lists */
node append_bll(node x, node y)
    /* requires y::sll<m,s2,b2> & x=null  */
    /* ensures res::sll<m,s2,b2>; */
	/* requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2 */
	/* ensures res::sll<nn+m, s0, b2>; */
    /* requires x::ll0<> * y::ll0<> */
	/* ensures res::ll0<>; */
             infer[H4,H5,H6]
  requires H4(x)*H5(y)
             ensures H6(res,y);
{
        node xn; 
        if (x==null) return y; /* segmentation bug when returning null */
        else {
         xn = append_bll(x.next,y);
         x.next = xn;
         return x;
        }
}


void qsort(ref node xs)
    requires xs=null
	ensures  xs'=null;
	requires xs::bnd<n, sm, bg> & n>0 
	ensures xs'::sll<n, smres, bgres> & smres >= sm & bgres < bg;
{
	node tmp;
        int v;
	bool b;

	if (xs != null)
	{
        v = xs.val;
		bind xs to (xsval, xsnext) in {
			tmp = partition(xsnext, v);
		}
        b = (xs.next == null);
		if (tmp != null)
      {
			qsort(tmp);}

		tmp = new node(v, tmp);
		if (b)
			xs = tmp;
		else
		{
			bind xs to (xsval, xsnext) in {
				qsort(xsnext);
			}
			//dprint;
			xs = append_bll(xs.next, tmp);
		}
	}

}
