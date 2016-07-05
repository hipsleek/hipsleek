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

requires p::cll<n> & Term
ensures true;

{
	int index = 0;
	if (p != null) {
		if (p.val == x)
			return index;
		return find_r (p.next, p, x, index + 1);
	}
	else
		return -1;
}

int find_r (node p, node q, int x, int index)

requires p::lseg<q, n> & Term[n] 
ensures true;

{
	if (p != q) {
		if (p.val == x)
			return index;
		return find_r (p.next, q, x, index + 1);
	}
	else
		return -1;
}
