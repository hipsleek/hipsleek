/* merge sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or
                  self::node<d, null> & n = 1 & sm <= d <= bg or 
                  self::node<d, p> * p::bnd<n-1, sm, bg> & p != null & sm <= d < bg 
               inv n >= 0; 

sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or
                  self::node<sm, q> * q::sll<n-1, qs, lg> & q != null & sm <= qs
               inv n >= 1 & sm <= lg;

/*ll1<n, S> == self =  null & S={} & n = 0
	or self::node<v, r> * r::ll1<n1, S1>  & n = n1+1 & S = union(S1, {v})
	inv n >= 0;

sll1<n, S> == self::node<v1, null> & S = {v1} & n = 1
	or self::node<v2, r> * r::sll1<n1, S1> & n = n1+1 & r != null 
	& S = union(S1, {v2}) &	forall(x: (x notin S1 | v2 <= x))
	inv n >= 1;*/
 

/* function to count the number of elements of a list */
int count(node x)
	requires x::bnd<n, sm, bg>
        ensures x::bnd<n, sm, bg> & res = n;

{
	int tmp;

	if (x == null)
		return 0;
	else
		return (1 + count(x.next));
}
/*
int count1(node x)
  requires x::ll1<n, S>
  ensures x::ll1<n, S> & res = n;

{
	int tmp;

	if (x == null)
		return 0;
	else
		return (1 + count1(x.next));
}*/

/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
node split(ref node x, int a)
	requires x::bnd<n, sm, bg> & a > 0 & n > a 
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
			tmp = split(xnext, a);
		}
		return tmp;
	}
}
/*
node split1(ref node x, int a)
  requires x::ll1<n, S> & a > 0 & n > a 
  ensures x'::ll1<n1, S1> * res::ll1<n2, S2> & n = n1 + n2 & n1 > 0 & n2 > 0 /*& n1 = a*/ & S = union(S1, S2); 

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
			tmp = split1(xnext, a);
		}
		return tmp;
	}
}
*/
int div2(int c) requires true ensures res + res = c;

/* merge sort */
node merge_sort(node xs)
	requires xs::bnd<n, sm, bg> & n > 0 
	ensures res::sll<n, smres, bgres> & smres >= sm & bgres <= bg;
{
	int c, middle;
	node s1, s2, s3; 

	if (xs.next != null) 
	{
		c = count(xs);
		middle = div2(c);
		s1 = split(xs, middle);
		s2 = merge_sort(s1);
		s3 = merge_sort(xs);
		return merge(s2, s3);
	}
	else {
		return xs;
	}
}
/*
node merge_sort1(node xs)
	requires xs::ll1<n, S> & n>0
	ensures res::sll1<n, S>;
{
	int c, middle;
	node s1, s2, s3; 

	if (xs.next != null) 
	{
		c = count1(xs);
		middle = div2(c);
		s1 = split1(xs, middle);
		s2 = merge_sort1(s1);
		s3 = merge_sort1(xs);
	        return merge1(s2, s3);
	}
	else {
		return xs;
	}
	
}
*/
node merge(node x1, node x2)
	requires x1::sll<n1, s1, b1> * x2::sll<n2, s2, b2>
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
				return merge(x1, x2.next);
			else
				return x1;
		}
	}
}
/*
node merge1(node x1, node x2)
	requires x1::sll1<n1, S1> * x2::sll1<n2, S2>
	ensures res::sll1<n1+n2, S3> & S3 = union(S1, S2);
{
	if (x2 == null)
		return x1; 
	else
	{
		if (x1 == null)
			return x2;
		else
		{
			x1 = insert1(x1, x2.val);
			if (x2.next != null)
				return merge1(x1, x2.next);
			else
				return x1;
		}
	}
}
*/
/* function to insert an element in a sorted list */
node insert(node x, int v)
	requires x::sll<n, xs, xl> & n > 0
	ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres =  max(v, xl);
{
	node tmp_null = null;
	node tmp;	

	if (v <= x.val)
		return new node(v, x);
	else
	{
		if (x.next != null)
		{
			tmp = insert(x.next, v);
			x.next = tmp;
		}
		else
			x.next = new node(v, tmp_null);
		
		return x;
	}
}

/*
node insert1(node x, int v)
	requires x::sll1<n, S>
	ensures res::sll1<n+1, S1> & S1 = union(S, {v});
{
	node tmp_null = null;
	node tmp;	

	if (v <= x.val)
		return new node(v, x);
	else
	{
		if (x.next != null)
		{
			tmp = insert1(x.next, v);
			x.next = tmp;
		}
		else
			x.next = new node(v, tmp_null);
		
		return x;
	}
}
*/

/* non-working */

/*
node merge_sort_1(node xs)
	requires xs::bnd<n, sm, bg> & n > 0 
	ensures res::sll<n, smres, bgres> & smres >= sm & bgres <= bg;
{
	int c, middle;
	node s1, s2, s3; 

	c = count(xs);
	if (c > 1) 
	{
		middle = div2(c);
		s1 = split(xs, middle);
		s2 = merge_sort(s1);
		s3 = merge_sort(xs);
		return merge(s2, s3);
	}
	else {
		// this requires coercion
		return xs;
	}
}
*/

