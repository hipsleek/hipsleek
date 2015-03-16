/* merge sort */

data node {
	int val; 
	node next; 
}

ll<n, S> == self =  null & S={} & n = 0
	or self::node<v, r> * r::ll<n1, S1>  & n = n1+1 & S = union(S1, {v})
	inv n >= 0;

sll<n, S> == self::node<v1, null> & S = {v1} & n = 1
	or self::node<v2, r> * r::sll<n1, S1> & n = n1+1 
	& S = union(S1, {v2}) &	forall(x: (x notin S1 | v2 <= x))
	inv n >= 1 & self!=null  & S!={} ;
 

/* function to count the number of elements of a list */
int count1(node x)
  requires x::ll<n, S>
  ensures x::ll<n, S> & res = n;

{
	int tmp;

	if (x == null)
		return 0;
	else
		return (1 + count1(x.next));
}

/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
node split1(ref node x, int a)
  requires x::ll<n, S> & a > 0 & n > a 
  ensures x'::ll<n1, S1> * res::ll<n2, S2> & n = n1 + n2 & n1 > 0 & n2 > 0 /*& n1 = a*/ & S = union(S1, S2); 

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
	requires xs::ll<n, S> & n>0
	ensures res::sll<n, S>;
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
	requires x1::sll<n1, S1> * x2::sll<n2, S2>
	ensures res::sll<n1+n2, S3> & S3 = union(S1, S2);
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
	requires x::sll<n, S>
	ensures res::sll<n+1, S1> & S1 = union(S, {v});
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


