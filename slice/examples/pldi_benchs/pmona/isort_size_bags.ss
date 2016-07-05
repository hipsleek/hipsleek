/* insertion sort */

data node {
	int val; 
	node next; 
}

ll<n, S> == 
	self = null & n = 0 & S = {} 
	or self::node<v, r> * r::ll<n1, S1> & n = 1 + n1 & S = union(S1, {v})
	inv n >= 0;

sll<n, S> == 
	self::node<v1, null> & n = 1 & S = {v1}
	or self::node<v2, r> * r::sll<n1, S1> & r != null 
	& S = union(S1, {v2}) &	forall(x: (x notin S1 | v2 <= x)) & n = n1 + 1
	inv n >= 1 & self !=null & S != {};
  
/* function to insert an element in a sorted list */
node insert(node x, int v)
	requires x::sll<n, S> & n > 0 
    ensures res::sll<n+1, S1> & S1 = union(S, {v});

{
        node tmp_null = null;
        node xn;

   if (v <= x.val) {
		return new node(v, x);
        }
	else {
      // assume false;
		if (x.next != null)
		{
            xn = insert(x.next, v);
			x.next = xn;
			return x;
		}
		else
		{
			x.next = new node(v, tmp_null);
			return x;
		}
    }
}

/* insertion sort */
void insertion_sort(node x, ref node y)
	requires x::ll<n1, S1> * y::sll<n2, S2>
    ensures y'::sll<n1+n2, S> * x::ll<n1, S1> & S = union(S1, S2);

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}


