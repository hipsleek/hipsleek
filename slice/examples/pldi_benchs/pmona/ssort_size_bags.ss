/* selection sort */

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
                 
int find_min(node x)
	requires x::ll<n, S> & n>0
    ensures x::ll<n, S> & res in S & forall(z: (z notin S | res <= z));
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
	requires x::ll<n, S> & a in S & x != null
	ensures x'::ll<n-1, S1> & S = union(S1, {a});
{
	if (x.val == a)
		x = x.next;
	else { 
		if (x.next != null)
			bind x to (_, xnext) in {
				delete_min(xnext, a);
			}
	}
}

node selection_sort(ref node x)
	requires x::ll<n, S> & x != null 
	ensures res::sll<n, S> & x' = null;

{
	int minimum;
	
	if (x == null) 
		return null;
	else {
		minimum = find_min(x);
		delete_min(x, minimum);

		if (x == null)
			return new node(minimum, null);
		else
		{  
			return new node(minimum, selection_sort(x));
		}
	}
}








