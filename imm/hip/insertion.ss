/* insertion sort */

data node {
	int val; 
	node next; 
}


bnd<n, sm, bg, a1, a2> == self = null & n = 0 or 
  self::node<d@a1, p@a2> * p::bnd<n-1, sm, bg,a1,a2> & sm <= d < bg
               inv n >= 0;


sll<n, sm, lg, a1, a2> == self::node<sm@a1, v@a2> & sm = lg & n = 1 & v=null or 
  self::node<sm@a1, q@a2> * q::sll<n-1, qs, lg,a1,a2> & q != null & sm <= qs
               inv n >= 1 & sm <= lg; 
     
/* function to insert an element in a sorted list */
node insert(node x, int v)
  requires x::sll<n, xs, xl, @L, @M> & n > 0 
  ensures res::sll<n+1, sres, lres, @A, @M> & sres = min(v, xs) & lres = max(v,xl);

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

/* insertion sort */
void insertion_sort(node x, ref node y)
  requires x::bnd<n1, sm1, bg1,@L,@M> * y::sll<n2, sm2, bg2,@L,@M>
  ensures y'::sll<n1+n2, sm, bg,@A,@M> * x::bnd<n1, sm1, bg1,@A,@M> & sm <= sm2 & bg >= bg2;

{
	if (x != null)
	{
		y = insert(y, x.val);
                dprint; 
		insertion_sort(x.next, y);
	}
}














































