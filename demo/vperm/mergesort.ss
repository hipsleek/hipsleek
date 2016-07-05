/*

   Description: Well-known parallel merge sort algorithm

*/

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or
                  self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d <= bg 
               inv n >= 0; 

sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or
                  self::node<sm, q> * q::sll<n-1, qs, lg> & sm <= qs
               inv n >= 1 & sm <= lg & self!=null;
 
/* function to count the number of elements of a list */
int count(node x)
  requires x::bnd<n, sm, bg> // & @value[x]
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
  requires x::bnd<n, sm, bg> & a > 0 & n > a // & @value[a] & @full[x]
  ensures x'::bnd<n1, sm, bg> * res::bnd<n2, sm, bg> & n = n1 + n2 & n1 > 0 & n2 > 0 & n1 = a; // & @full[x]; //'

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

int div2(int c) 
  requires true //@value[c] 
  ensures res + res = c;

node merge(node x1, node x2)
  requires x1::sll<n1, s1, b1> * x2::sll<n2, s2, b2> // & @value[x1,x2]
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
				assert tmp'::sll<n1+n2,_,max(b1,b2)>  ; //'
				return tmp;
			}
			else
				return x1;
		}
	}
}

/* function to insert an element in a sorted list */
node insert(node x, int v)
  requires x::sll<n, xs, xl> & n > 0 //& @value[x,v]
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

void parallel_merge_sort2(node xs,ref node ys)
  requires xs::bnd<n, sm, bg> & n > 0 // & @value[xs] & @full[ys]
	ensures ys'::sll<n, smres, bgres> & smres >= sm & bgres <= bg; // & @full[ys]; //'
{
	int c, middle;
	node s1, s2, s3;

	if (xs.next != null)
	{
		c = count(xs);
		middle = div2(c);
		s1 = split_func(xs, middle);
        // xs contains up to middle elements
        // s1 is the rest
        int id1,id2;
        id1 = fork(parallel_merge_sort2,s1,s2);
        id2 = fork(parallel_merge_sort2,xs,s3);
        join(id1);
        join(id2);
        ys = merge(s2,s3);
	}
	else {
        ys = xs;
	}
}
