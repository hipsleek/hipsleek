/* quick sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg,a1,a2> == self = null & n = 0 or 
  self::node<d@a1, p@a2> * p::bnd<n-1, sm, bg,a1,a2> & sm <= d < bg 
      inv n >= 0;

sll<n, sm, lg, a1, a2> == 
     self::node<qmin@a1, nx@a2> & qmin = sm & qmin = lg & n = 1 & nx=null
  or self::node<sm@a1, q@a2> * q::sll<n-1, qs, lg,a1,a2> &  sm <= qs 
      inv n >= 1 & sm <= lg & self!=null ;

node partition(ref node xs, int c)
  requires xs::bnd<n, sm, bg,@L,@M> & sm <= c <= bg
    ensures xs'::bnd<a, sm, c,@A,@M> * res::bnd<b, c, bg,@A,@M> & n = a+b;
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

/* function to append 2 bounded lists */
node append_bll(node x, node y)
    requires y::sll<m,s2,b2,@L,@M> & x=null 
    ensures res::sll<m,s2,b2,@A,@M>;
	requires x::sll<nn, s0, b0,@L,@M> * y::sll<m, s2, b2,@L,@M> & b0 <= s2
	ensures res::sll<nn+m, s0, b2,@A,@M>;

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
	requires xs::bnd<n, sm, bg,@L,@M> & n>0 
	ensures xs'::sll<n, smres, bgres,@A,@M> & smres >= sm & bgres < bg;
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
