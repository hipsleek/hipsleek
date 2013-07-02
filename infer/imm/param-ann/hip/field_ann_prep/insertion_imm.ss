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
    requires x::sll<n, xs, xl>@I  & n > 0 
    ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres = max(v,xl);

{
        node tmp_null = null;
        node xn;
	node tmp;

   if (v <= x.val) {
		    //assume false;
		return new node(v, copy(x));
        }
	else {
       //assume false;
		if (x.next != null)
		{
	       
		        xn = insert(x.next, v);
			//x.next = xn;
			tmp = new node(x.val, xn);
			return tmp;
		}
		else
		{
		        xn = new node(v, tmp_null);
			tmp = new node(x.val, xn); 
			//x.next = new node(v, tmp_null);
			//return x;
			return tmp;
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


/* insertion sort */
node insertion_sort(node x, node y)
	requires (x::bnd<n1, sm1, bg1>@I & y::sll<n2, sm2, bg2>@I)
        ensures res::sll<n1+n2, sm, bg> & sm <= sm2 & bg >= bg2;

{
 
	if (x != null)
	{
		node tmp  = insert(y, x.val);
		return insertion_sort(x.next, tmp);
	}
	else {return copy(y);}
}














































