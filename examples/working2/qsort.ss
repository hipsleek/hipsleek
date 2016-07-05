/* quick sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or 
                  self::node<d, p> * p::bnd<n1, sm, bg> & n= n1+1 & sm <= d < bg 
               inv n >= 0;

sll<n, sm, lg> == self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 or 
                  self::node<sm, q> * q::sll<n1, qs, lg> & n= n1+1 & q != null & sm <= qs 
               inv n >= 1; // & sm <= lg;

node partition(ref node xs, int c)
	requires xs::bnd<n, sm, bg> & sm <= c <= bg
    ensures xs'::bnd<a, sm, c> * res::bnd<b, c, bg> & n = a+b;
{
	node tmp1;
	int v; 

	if (xs == null)
		return null;
	else
	{
		if (xs.val >= c)
		{
            v = xs.val;
			bind xs to (xsval, xsnext) in {
				tmp1 = partition(xsnext, c);
			}
			
			// xs.next has been updated to point to the "less than" partition.
			// xs itself belongs to the "greater than" partition, which is pointed
			// to by tmp1.
			// xs must be updated to point to the "less than" partition.

			node tmp2 = xs;
			xs = xs.next;
			tmp2.next = tmp1;
			return tmp2;
		}
		else {
			bind xs to (xsval, xsnext) in {
				tmp1 = partition(xsnext, c);
			}
			return tmp1;
		}
	}
}

/* function to append 2 bounded lists */
node append_bll(node x, node y)
	requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2
	ensures res::sll<nn+m, s0, b2>;

{
        node xn; 

	if (x.next == null)
		x.next = y;
	else
         {
		xn = append_bll(x.next, y);
                x.next = xn;
         }

	return x; 
}


void qsort(ref node xs)
	requires xs::bnd<n, sm, bg> & n>0 
	ensures xs'::sll<n, smres, bgres> & smres >= sm & bgres < bg;

{
	node tmp, tmp2;
    int v;
	bool b;

	if (xs != null)
	{
        v = xs.val; // v is the pivot

		bind xs to (xsval, xsnext) in {
			tmp = partition(xsnext, v);
		}

        b = (xs.next == null);
		if (tmp != null)
			qsort(tmp);

		tmp2 = xs.next; // tmp2 points to the list of elements smaller than xs.val

		xs.next = tmp; // tmp points to the sorted list of elements greater than xs.val,
		tmp = xs; // so put xs as the first element of the list.

		if (tmp2 != null)
		{
			qsort(tmp2);
			xs = append_bll(tmp2, tmp);
		}
	}	
}

