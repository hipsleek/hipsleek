/************************************************************************
Example from "Looper: Lightweight Detection of Infinite Loops at Runtime"
Jacob Burnim et al. (ASE'09)
*************************************************************************/

data node {
	int val;
	node next;
}

lseg<p, n> == 
	self = p & n = 0 or 
	self::node<v, r> * r::lseg<p, n-1> & self != p  
	inv n >= 0;

cll<n> == 
	self = null & n = 0 or 
	self::node<v, r> * r::lseg<self, n-1>   
	inv n >= 0;

int find (node p, int x)
/*
requires p::node<_, p> & MayLoop
ensures true;
*/
requires p::node<y, p> & x!=y & Loop
ensures false;
{
	int index = 0;
	if (p != null) {
		if (p.val == x)
			return index;
		return find (p.next, x);
	}
	else
		return -1;
}
