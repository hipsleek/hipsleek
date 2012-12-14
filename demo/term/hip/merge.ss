/* merge sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or
                  self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d <= bg 
               inv n >= 0; 

/*

bnd<n, sm, bg> == self = null & n = 0 or
                  self::node<d, null> & n = 1 & sm <= d <= bg or 
                  self::node<d, p> * p::bnd<n-1, sm, bg> & p != null & sm <= d <= bg 
               inv n >= 0; 
*/


sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or
                  self::node<sm, q> * q::sll<n-1, qs, lg> & sm <= qs
               inv n >= 1 & sm <= lg & self!=null;
 
/* function to count the number of elements of a list */
int count(node x)
	requires x::bnd<n, sm, bg>
    variance (1) [n]
    ensures x::bnd<n, sm, bg> & res = n;
{
	int tmp;

	if (x == null)
		return 0;
	else
		return (1 + count(x.next));
}

/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
node split_func(ref node x, int a)
	requires x::bnd<n, sm, bg> & a > 0 & n > a
    variance (1) [n]
    ensures x'::bnd<n1, sm, bg> * res::bnd<n2, sm, bg> & n = n1 + n2 & n1 > 0 & n2 > 0 & n1 = a; 

{
	node tmp;

	if (a == 1)
	{
		tmp = x.next; 
		x.next = null;
		return tmp;
	}
	else
	{
		a = a - 1;
		node tmp;
		bind x to (_, xnext) in {
			tmp = split_func(xnext, a);
		}
		return tmp;
	}
}

int div2(int c) requires true ensures res + res = c;

/* merge sort */
node merge_sort(node xs)
	requires xs::bnd<n, sm, bg> & n > 0
    variance (1) [n]
	ensures res::sll<n, smres, bgres> & smres >= sm & bgres <= bg;
{
	int c, middle;
	node s1, s2, s3; 

	if (xs.next != null) 
	{
		c = count(xs);
		middle = div2(c);
		s1 = split_func(xs, middle);
		s2 = merge_sort(s1);
		s3 = merge_sort(xs);
		return merge(s2, s3);
	}
	else {
		return xs;
	}
}

node merge(node x1, node x2)
	requires x1::sll<n1, s1, b1> * x2::sll<n2, s2, b2>
    variance (1) [n2]
	ensures res::sll<n1+n2, s3, b3> & s3 = min(s1, s2) & b3 = max(b1, b2);
{
	if (x2 == null)
		return x1; 
	else
	{
		if (x1 == null)
			return x2;
		else
		{
			x1 = insert(x1, x2.val);
			if (x2.next != null)
			{
				node tmp = merge(x1, x2.next);
				//dprint;
				assert tmp'::sll<n1+n2,_,max(b1,b2)>  ;
				return tmp;
			}
			else
				return x1;
		}
	}
}

/* function to insert an element in a sorted list */
node insert(node x, int v)
	requires x::sll<n, xs, xl> & n > 0
    variance (1) [n]
	ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres =  max(v, xl);
{
	node tmp;	

	if (v <= x.val)
		return new node(v, x);
	else
	{
		if (x.next != null)
		{
			x.next = insert(x.next, v);
      return x;
		}
		else
    {
			x.next = new node(v,null);
      return x;
    }
	}
}
