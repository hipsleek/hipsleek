/* merge sort */

data node {
	int val; 
	node next; 
}

/*
bnd<n, sm, bg> == self = null & n = 0 or
                  self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d <= bg 
               inv n >= 0; 



bnd<n, sm, bg> == self = null & n = 0 or
                  self::node<d, null> & n = 1 & sm <= d <= bg or 
                  self::node<d, p> * p::bnd<n-1, sm, bg> & p != null & sm <= d <= bg 
               inv n >= 0; 



sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or
                  self::node<sm, q> * q::sll<n-1, qs, lg> & sm <= qs
               inv n >= 1 & sm <= lg & self!=null;
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
 
node merge(node x1, node x2)
	requires x1::sll<n1, s1, b1> * x2::sll<n2, s2, b2>
	ensures res::sll<n1+n2, s3, b3> & s3 = min(s1, s2) & b3 = max(b1, b2);
{
	if (x2 == null)
		return x1; 
	else
	{
		if (x1 == null)
			return x2;
		else
		{
			x1 = insert(x1, x2.val);
			if (x2.next != null)
			{
				node tmp = merge(x1, x2.next);
				//dprint;
				assert tmp'::sll<n1+n2,_,max(b1,b2)>  ;
				return tmp;
			}
			else
				return x1;
		}
	}
}

/* function to insert an element in a sorted list */
node insert(node x, int v)
	requires x::sll<n, xs, xl> & n > 0
	ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres =  max(v, xl);
/*
{
	node tmp;	

	if (v <= x.val)
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
*/

