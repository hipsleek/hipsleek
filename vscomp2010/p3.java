/**
 Problem 3 in VSComp 2010: Searching a Linked List
 @author Vu An Hoa
 @date 24/06/2011
 **/

data llist 
{
	int value;
	llist ltail;
}

// Linked list with the first occurence of zero at index z
// or no zero and z = n
llz<n,z> == self = null & n = 0 & z = 0
	or self::llist<0,t> * t::llz<n-1,_> & z = 0 & n >= 1
	or self::llist<v,t> * t::llz<n-1,z-1> & v != 0 & n >= 1
	inv n >= 0 & 0 <= z & z <= n;

int search(llist L)
	requires L::llz<n,z>
	ensures res = z;
{
	return search_helper(L, 0);
}

int search_helper(llist L, int d)
	requires L::llz<n,z>
	ensures res = z + d;
{
	if (L == null)
		return d;
	else if (L.value == 0)
		return d;
	else
		return search_helper(L.ltail,d+1);
}
