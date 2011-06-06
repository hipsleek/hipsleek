/* quick sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or 
      self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d <= bg 
      inv n >= 0;

sll<n, sm, lg> == 
     self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 
  or self::node<sm, q> * q::sll<n-1, qs, lg> &  sm <= qs 
      inv n >= 1 & sm <= lg & self!=null ;

//   bnd(sm,c)    bnd(c,bg)
//   sll(s1,l1)&sm<=s1&l1<=c  sll(s2,l2) & c<=s2 & l2<=bg

node partition(ref node xs, int c)
  requires xs::bnd<n, sm, bg> & sm <= c <= bg
  ensures xs'::bnd<a, sm, c> * res::bnd<b, c, bg> & n = a+b;
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
    requires y::sll<m,s2,b2> & x=null 
    ensures res::sll<m,s2,b2>;
	requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2
	ensures res::sll<nn+m, s0, b2>;

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
    //requires xs=null
	//ensures  xs'=null;
	requires xs::bnd<n, sm, bg> & n>0 
	ensures xs'::sll<n, smres, bgres> & sm<=smres & bgres <= bg;
{
	node tmp;
        int v;
	bool b;

	if (xs != null)
	{
        v = xs.val;
        tmp = partition(xs,v);
		if (tmp != null)
        {
			qsort(tmp);
        }
        else {
            assume true;
        }

		if (xs == null)
			xs = tmp;
		else
		{
			qsort(xs);
            dprint;
            assume false;
			xs = append_bll(tmp, xs);
		}
	}

}
