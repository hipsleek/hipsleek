data node{
	int val;
	node next;
}

ll<> == self = null
	or self::node<_,p> * p::ll<>
inv true;

global node SENTINEL;

void traverse(node c, node p)
requires c::node<_,cn> * cn::ll<> * p::ll<>
ensures c::ll<> * p::ll<>;
{
	node n;
	if (c != SENTINEL){ 
		if(c != null){
		//assume false;
		n = c.next;
		c.next = p;
		p = c;
		c = n;
//		dprint;
		}
		if (c == null){
			c = p;
			p = null;
		}
		//traverse(c,p);
	}
//	dprint;
}

void trav(node root)
requires root::ll<> * SENTINEL::node<_,null>
ensures root::ll<>;
{
	if (root == null) return;
	else {
		node prev = SENTINEL;
		node curr = root;
//		dprint;
		traverse(curr,prev);
	}
//dprint;
}
