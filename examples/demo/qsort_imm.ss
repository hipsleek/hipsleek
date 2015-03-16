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

node partition(node xs, int c, ref node r)
    requires xs::bnd<n, sm, bg>@I & sm <= c <= bg
    ensures r'::bnd<a, sm, c> * res::bnd<b, c, bg> & n = a+b;
{
	node tmp1, tmp2;
	int v; 

	if (xs == null) {
		r = null;
		return null;
	}
	else
	{
		if (xs.val >= c)
		{
		        v = xs.val;
			tmp1 = partition(xs.next, c, tmp2);
			r = tmp2;
			return new node(v, tmp1);
		}
		else {
			tmp1 = partition(xs.next, c, tmp2);
			r = new node(xs.val, tmp2);
			return tmp1;
		}
	}
}

node copy(node x) 
requires x::sll<n,sm,bg>@I
ensures res::sll<n,sm,bg>;
{
 node tmp1, tmp2;
 if (x.next==null) return new node(x.val, null);
    else {
	  tmp1 = copy(x.next);
	  tmp2 = new node(x.val, tmp1);
	      return tmp2;
	      }
}


/* function to append 2 bounded lists */
node append_bll(node x, node y)
    requires y::sll<m,s2,b2> & x=null 
    ensures res::sll<m,s2,b2>;
	requires (x::sll<nn, s0, b0>@I & y::sll<m, s2, b2>@I) & b0 <= s2
	ensures res::sll<nn+m, s0, b2>;

{
        node xn; 
        if (x==null) return copy(y); /* segmentation bug when returning null */
        else {
         xn = append_bll(x.next,copy(y));   
         return new node(x.val, xn);
        }
}


node qsort(node xs)
    requires xs=null
    ensures  res=null;
    requires xs::bnd<n, sm, bg>@I & n>0 
    ensures res::sll<n, smres, bgres> & smres >= sm & bgres < bg;
{
	node tmp1, tmp2;
        int v;
	bool b;

	if (xs != null)
	{
	 v = xs.val;
	 tmp2 = partition(xs.next, v, tmp1);
         b = (tmp1 == null);
	 if (tmp2 != null)
	 {
	       tmp2 = qsort(tmp2);
	 }

	 tmp2 = new node(v, tmp2);
	 if (b)
			return tmp2;
	 else
	 {
			tmp1 = qsort(tmp1);
			return append_bll(tmp1, tmp2);
	 }
	}
	else
	return null;

}

