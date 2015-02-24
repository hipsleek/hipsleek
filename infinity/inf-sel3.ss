/* selection sort */

data node {
	int val; 
	node next; 
}

bnd1<n, mi> == self = null & n = 0 & mi = \inf or 
        self::node<d, p> * p::bnd1<n-1, tmi> & mi = min(d, tmi) & -\inf<d<\inf
            inv n >= 0;

sll<n, sm> == self = null & sm = \inf & n = 0 or 
               self::node<sm, q> * q::sll<n-1, qs> & sm <= qs
               inv n >= 0; 
                 
int find_min(node x)
    requires x::bnd1<n, mi> & n > 0
    ensures x::bnd1<n, mi> & res = mi;
{
	int tmp; 

	if (x.next == null)
		return x.val;
	else
	{	
		tmp = find_min(x.next);
		if (tmp > x.val)
			return x.val;
		else
			return tmp;
	}
}

void delete_min(ref node x, int a)
	requires x::bnd1<n, mi> & n >= 1 & a = mi
        case 
        { n=1 -> ensures x'=null; //=null;
          n!=1 -> ensures x'::bnd1<n-1, mi1> & mi1>=mi;
        }
       /*
	ensures x'::bnd1<n-1, mi1> 
                & mi1>=mi 
               //&(n=1 & mil=\inf | n>1 & mi1 >= mi)
               ;//'
        */
{
	if (x.val == a)
		x = x.next;
	else {
                //assume xnext'=null or xnext'!=null;
		bind x to (_, xnext) in {
			delete_min(xnext, a);
		}
	}
}

node selection_sort(ref node x)
	requires x::bnd1<n, mi> & n > 0 
	ensures res::sll<n, mi> & x' = null;

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












