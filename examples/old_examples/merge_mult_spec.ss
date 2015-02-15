/* merge sort */

data node {
	int val; 
	node next; 
}

 /*sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or
                  self::node<sm, q> * q::sll<n-1, qs, lg> & q != null & sm <= qs
               inv n >= 1 & sm <= lg;*/

bnd<n, sm, bg> == self = null & n = 0 or
                  self::node<d, null> & n = 1 & sm <= d <= bg or 
                  self::node<d, p> * p::bnd<n-1, sm, bg> & p != null & sm <= d < bg 
               inv n >= 0; 
 
//*********************** FOR MULTIPLE SPEC **************************************************
sll<sm, lg> == self::node<sm, null> & sm = lg or
               self::node<sm, q> * q::sll<qs, lg> & q != null & sm <= qs
               inv sm <= lg;

ll<n> == self = null & n = 0 or
	self::node<_, q> * q::ll<n-1> & n > 0
	inv n >= 0; 

/* function to count the number of elements of a list */
int count(node x)
	requires x::bnd<n, sm, bg>
        ensures x::bnd<n, sm, bg> & res = n;

	requires x::ll<n>
	ensures x::ll<n> & res = n;

{
	int tmp;

	if (x == null)
		return 0;
	else
		return (1 + count(x.next));
}

/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
node split(ref node x, int a)
	requires x::bnd<n, sm, bg> & a > 0 & n > a 
        ensures x'::bnd<n1, sm, bg> * res::bnd<n2, sm, bg> & n = n1 + n2 & n1 > 0 & n2 > 0 & n1 = a; 
	//*********************** FOR MULTIPLE SPEC **************************************************
	requires x::ll<n> & a > 0 & n > a
	ensures x'::ll<a> * res::ll<n-a>; 

{
	node tmp;

	if (a == 1)
	{
		if(x != null) {
			tmp = x.next; 
			x.next = null;
			return tmp;
		}
		else return null;
	}
	else
	{
		a = a - 1;
		node tmp;
		if (x != null) {
			//assume false;
			bind x to (_, xnext) in {
				tmp = split(xnext, a);
			}
		}
		else { tmp = null;}
		return tmp;
	}
}

int div2(int c) requires true ensures res + res = c;

/* merge sort */
node merge_sort(node xs)
	/*requires xs::bnd<n, sm, bg> & n > 0 
	ensures res::sll<n, smres, bgres> & smres >= sm & bgres <= bg;*/
	//*********************** FOR MULTIPLE SPEC **************************************************
	requires xs::bnd<_, sm, bg> & xs != null 
	ensures res::sll<smres, bgres> & smres >= sm & bgres <= bg;
	
	requires xs::ll<n> & n > 0 
	ensures res::ll<n>;
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

node merge(node x1, node x2)
	/*requires x1::sll<n1, s1, b1> * x2::sll<n2, s2, b2>
	ensures res::sll<n1+n2, s3, b3> & s3 = min(s1, s2) & b3 = max(b1, b2);*/
	//*********************** FOR MULTIPLE SPEC **************************************************
	requires x1::sll<s1, b1> * x2::sll<s2, b2>
	ensures res::sll<s3, b3> & s3 = min(s1, s2) & b3 = max(b1, b2);
	
	requires x1::ll<n1> * x2::ll<n2>
	ensures res::ll<n1+n2>;
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

/* function to insert an element in a sorted list */
node insert(node x, int v)
	/*requires x::sll<n, xs, xl> & n > 0
	ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres =  max(v, xl);*/
	//*********************** FOR MULTIPLE SPEC **************************************************
	requires x::sll<xs, xl> 
	ensures res::sll<sres, lres> & sres = min(v, xs) & lres =  max(v, xl);
	
	requires x::ll<n> & n > 0
	ensures res::ll<n+1>;
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
