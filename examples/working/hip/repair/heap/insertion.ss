data node {
	int val; 
	node next; 
}

  sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or 
                  self::node<sm, q> * q::sll<n-1, qs, lg> & q != null & sm <= qs
               inv n >= 1 & sm <= lg; 

node insert(node x, int v)
	requires x::sll<n, xs, xl> & n > 0 
  ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres = max(v,xl);
{

   if (v <= x.val) {
		return new node(v, x);
        }
	else {
		if (x.next != null)
		{
      node xn;
      xn = insert(x.next, v);
			x.next = xn;
			return x.next;
		}
		else{
			x.next = new node(v, null);
			return x;
		}
    }
}

// void insertion_sort(node x, node@R y)
// 	requires x::bnd<n1, sm1, bg1> * y::sll<n2, sm2, bg2>
//   ensures y'::sll<n1+n2, sm, bg> * x::bnd<n1, sm1, bg1> & sm <= sm2 & bg >= bg2;

// {
// 	if (x != null)
// 	{
// 		y = insert(y, x.val);
// 		insertion_sort(x.next, y);
// 	}
// }