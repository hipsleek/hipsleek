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
	requires x::bnd1<n, s, l, mi> & n>0
    variance (1) [n]
    ensures x::bnd1<n, s, l, mi> & res = mi;
{
	int tmp; 

	if (x.next == null)
		return x.val;
	else
	{		assume false;
		tmp = find_min(x.next);
		if (tmp > x.val)
			return x.val;
		else
			return tmp;
	}
}

void delete_min(ref node x, int a)
	requires x::bnd1<n, s, l, mi> & n >= 1 & a = mi
    variance (1) [n]
	ensures x' = null & n = 1 & s <= mi < l or 
                x'::bnd1<n-1, s, l, mi1> & mi1 >= mi & x' != null & n > 1;

{
	if (x.val == a)
		x = x.next;
	else {
		bind x to (_, xnext) in {
			delete_min(xnext, a);
		}
	}
}

node selection_sort(ref node x)
	requires x::bnd1<n, sm, lg, mi> & n > 0
    variance (1) [n]
	ensures res::sll<n, mi, l> & l < lg & x' = null;

{
	int minimum;
	node tmp, tmp_null = null;	

	minimum = find_min(x);
	delete_min(x, minimum);

	if (x == null)
		return new node(minimum, tmp_null);
	else
	{
		tmp = selection_sort(x);

		return new node(minimum, tmp);
	}
}












