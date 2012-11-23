/* merge sort */

data node {
	int val; 
	node next; 
}

ll<n> == self = null & n = 0
	or self::node<v, r> * r::ll<n1> & n = n1+1	
	inv n >= 0;

sll<n> == self::node<v1, null> & n = 1
	or self::node<v2, r> * r::sll<n1> & n = n1+1 
	inv n >= 1 & self!=null;
	
bnd<n, sn, bg> == 
	    self=null & n=0 & sn = bg
	or  self::node<d,p> * p::bnd<n2,sn,bg> & n2 = n-1 & sn <= d < bg
	inv n>=0 & sn <= bg;
 

/* function to count the number of elements of a list */
int count1(node x)
  requires x::ll<n>
  ensures x::ll<n> & res = n;
{
	int tmp;

	if (x == null)
		return 0;
	else
		return (1 + count1(x.next));
}

/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
node split1(ref node x, int a)
  requires x::ll<n> & a > 0 & n > a 
  ensures x'::ll<n1> * res::ll<n2> & n = n1 + n2 & n1 > 0 & n2 > 0; 

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

int div2(int c) requires true ensures res + res = c;

/* merge sort */
node merge_sort1(node xs)
	requires xs::ll<n> & n>0
	ensures res::sll<n>;
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

node merge1(node x1, node x2)
	requires x1::sll<n1> * x2::sll<n2>
	ensures res::sll<n1+n2>;
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

/* function to insert an element in a sorted list */
node insert1(node x, int v)
	requires x::sll<n>
	ensures res::sll<n+1>;
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


