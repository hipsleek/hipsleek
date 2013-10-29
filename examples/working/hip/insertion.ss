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
     
/* function to insert an element in a sorted list */
node insert(node x, int v)
	requires x::sll<n, xs, xl> & n > 0 
    ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres = max(v,xl);

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
void insertion_sort(node x, node@R y)
	requires x::bnd<n1, sm1, bg1> * y::sll<n2, sm2, bg2>
        ensures y'::sll<n1+n2, sm, bg> * x::bnd<n1, sm1, bg1> & sm <= sm2 & bg >= bg2;

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}














































