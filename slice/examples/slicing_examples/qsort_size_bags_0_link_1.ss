/* quick sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg, S> == self = null & n = 0 & S = {} or 
      self::node<d, p> * p::bnd<n-1, sm, bg, S1> & sm <= d < bg & S = union(S1, {d}) 
      inv n >= 0;

sll<n, sm, lg, S> == 
     self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 & S = {sm} 
  or self::node<sm, q> * q::sll<n-1, qs, lg, S1> &  sm <= qs & S = union(S1, {sm}) & forall (x : (x notin S1 | sm <= x))
      inv n >= 1 & sm <= lg & self!=null;

node partition(ref node xs, int c)
  requires xs::bnd<n, sm, bg, S> & sm <= c <= bg
    ensures xs'::bnd<a, sm, c, S1> * res::bnd<b, c, bg, S2> & n = a+b & S = union(S1, S2);
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

    requires y::sll<m,s2,b2, S1> & x=null 
    ensures res::sll<m,s2,b2, S1>;
	requires x::sll<nn, s0, b0, S1> * y::sll<m, s2, b2, S2> & b0 <= s2
	ensures res::sll<nn+m, s0, b2, S> & S = union(S1, S2);

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
	requires xs::bnd<n, sm, bg, S> & n>0 
	ensures xs'::sll<n, smres, bgres, S> & smres >= sm & bgres < bg;
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
