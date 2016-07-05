/* quick sort */

data node {
	int val; 
	node next; 
}

/*
bnd<n, sm, bg> == self = null & n = 0 or 
      self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d < bg 
      inv n >= 0;

sll<n, sm, lg> == 
     self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 
  or self::node<sm, q> * q::sll<n-1, qs, lg> &  sm <= qs 
      inv n >= 1 & sm <= lg & self!=null ;
*/

bnd<n,mi,mx> == self = null & n = 0 & mi = \inf & mx=-\inf or 
  self::node<d, p> * p::bnd<n-1, tmi,tmx> & mi = min(d, tmi) & mx=max(d,tmx) & -\inf<d<\inf 
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n=1 & mi=mx & -\inf<mi<\inf |
      self!=null & n>1 & mi<=mx & -\inf<mi & mx<\inf;

sll<n, mi,mx> == 
   self = null & mi = \inf & mx = -\inf & n = 0
 or self::node<mi, null> & n=1 & -\inf<mi<\inf & mi=mx
 or self::node<mi, q> * q::sll<n-1, qs,mx> & -\inf<mi<\inf & mi <= qs
      &  q!=null 
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n>0 & mi<=mx  & -\inf<mi & mx<\inf;

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
