/* selection sort */

data node {
	int val; 
	node next; 
}

bnd1<n, sm, bg, mi> == self = null & n = 0 & mi = \inf & mi <= bg or 
               self::node<d, p> * p::bnd1<n-1, sm, bg, tmi> & sm <= d <= bg & mi = min(d, tmi) & sm <= mi <= bg
                    inv n >= 0 & sm <= mi <= bg;


void delete_min(ref node x, int a)
   requires x::bnd1<n, s, l, mi> & n >= 1 & a = mi
   case {
     n=1 -> ensures x'=null & s<=mi<=l;
     n!=1 -> ensures x'::bnd1<n-1, s, l, mi1> 
     //& n>1
     //& mi1 >= mi & n>1
              ;
    }
                //& x' != null & n > 1
{
	if (x.val == a)
		x = x.next;
	else {
		bind x to (_, xnext) in {
			delete_min(xnext, a);
		}
	}
}










