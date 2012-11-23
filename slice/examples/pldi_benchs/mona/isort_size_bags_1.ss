/* insertion sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg, S> == 
	self = null & sm = bg & n = 0 & S = {} or 
    self::node<d, p> * p::bnd<n-1, sm, bg, S1> & sm <= d < bg & S = union({d}, S1)
    inv n >= 0 & sm <= bg;

sll<n, sm, lg, S> == 
	self::node<sm, null> & sm = lg & n = 1 & S = {sm} or 
    self::node<sm, q> * q::sll<n-1, qs, lg, S1> & q != null & sm <= qs
	& S = union(S1, {sm}) & forall(x: (x notin S1 | sm <= x))
    inv n >= 1 & sm <= lg; 
  
/* function to insert an element in a sorted list */
node insert(node x, int v)
	requires x::sll<n, xs, xl, S> & n > 0 
    ensures res::sll<n+1, sres, lres, S1> & sres = min(v, xs) & lres = max(v,xl) & S1 = union(S, {v});

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
	requires x::bnd<n1, sm1, bg1, S1> * y::sll<n2, sm2, bg2, S2>
    ensures y'::sll<n1+n2, sm, bg, S> * x::bnd<n1, sm1, bg1, S1> & sm <= sm2 & bg >= bg2 & S = union(S1, S2);

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}














































