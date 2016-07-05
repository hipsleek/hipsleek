/* selection sort */

data node {
	int val; 
	node next; 
}

bnd1<n, sm, bg, mi> == self::node<mi, null> & sm <= mi < bg & n = 1 or
                       self::node<d, p> * p::bnd1<n-1, sm, bg, tmi> & sm <= d < bg & mi = min(d, tmi) & sm <= mi < bg
                    inv n >= 1 & sm <= mi < bg &self!=null;

sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or 
                  self::node<sm, q> * q::sll<n-1, qs, lg> & q != null & sm <= qs
               inv n >= 1 & sm <= lg & self!=null; 

                 
int find_min(node x)
	requires x::bnd1<n, s, l, mi>@I & n>0
        ensures res = mi;
{
	int tmp; 

	if (x.next == null) {
	        tmp = x.val;
		return tmp;
		}
	else
	{		
		tmp = find_min(x.next);
		if (tmp > x.val)
			return x.val;
		else
			return tmp;
	}
}

node copy(node x) 
requires x::bnd1<n,s,l,mi>@I 
ensures res::bnd1<n,s,l,mi>;
{
 node tmp1, tmp2;
 if (x.next==null) return new node(x.val, null);
    else {
	  tmp1 = copy(x.next);
	  tmp2 = new node(x.val, tmp1);
	      return tmp2;
	      }
}

node delete_min(node x, int a)
	requires x::bnd1<n, s, l, mi>@I & n >= 1 & a = mi 
	ensures res = null & n = 1 & s <= mi < l or 
                res::bnd1<n-1, s, l, mi1> & mi1 >= mi & res != null & n > 1;

{
        node tmp;
	if (x.val == a) {
	   if (x.next != null) return copy(x.next);
	   else {
		 tmp = null;
		 return tmp;
		 }
	   }
	else {
	      //assume false;
	      tmp = delete_min(x.next, a);
		  return new node(x.val, tmp);
	//	bind x to (_, xnext) in {
	//		delete_min(xnext, a);
	//	}
	}
}

node selection_sort(node x)
	requires x::bnd1<n, sm, lg, mi>@I & n > 0 
	ensures res::sll<n, mi, l> & l < lg;

{
	int minimum;
	node tmp, tmp1, tmp_null = null;	

	minimum = find_min(x);
	tmp1 = delete_min(x, minimum);

	if (tmp1 == null) {
			   //assume false;
		return new node(minimum, tmp_null);
	}
	else
	{
//	 assume false;
		tmp = selection_sort(tmp1);

		return new node(minimum, tmp);
	}
}












