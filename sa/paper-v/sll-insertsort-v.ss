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
