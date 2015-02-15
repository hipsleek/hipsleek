/* selection sort */

data node {
	int val; 
	node next; 
}

ll1<S> == self = null & S = {}
	or self::node<v2, r>* r::ll1<S1> & S = union(S1, {v2});

sll1<S> == self = null & S = {}
	or self::node<v2, r> * r::sll1<S1> & S = union(S1, {v2}) & 
	forall(x: (x notin S1 | v2 <= x));

//------------------------------------------------------------------------------------------
// find_min functions
//------------------------------------------------------------------------------------------
int find_min(node x)
requires x::ll1<S> & x != null
ensures x::ll1<S> & res in S & forall (a: (a notin S | res <= a)); // bagmin(res, S);
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
  
     
//------------------------------------------------------------------------------------------
// delete_min functions
//------------------------------------------------------------------------------------------
void delete_min(ref node x, int a)
	requires x::ll1<S> & a in S & x != null// bagmin(a, S)
	ensures x'::ll1<S1> & S = union(S1, {a});
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


//------------------------------------------------------------------------------------------
// selection_sort functions
//------------------------------------------------------------------------------------------

node selection_sort(ref node x)
	requires x::ll1<S> & x != null 
	ensures res::sll1<S> & x' = null;

{
	int minimum;
	
	minimum = find_min(x);
	if (x == null) 
		return null;
	else {
		delete_min(x, minimum);

		if (x == null)
			return new node(minimum, null);
		else
		{  
			return new node(minimum, selection_sort(x));
		}
	}
}












