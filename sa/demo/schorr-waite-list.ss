data node{
	int val;
	node next;
}

ll<> == self = null
	or self::node<_,p> * p::ll<>
inv true;

global node SENTINEL;

void traverse(ref node c, ref node p, ref node n)
requires c::node<_,n> * p::ll<> * n::ll<>
ensures n'::ll<> * p'::ll<> & c'= SENTINEL & SENTINEL' = SENTINEL; 
//& n' = c;
{
//	node n;
	if (c != SENTINEL){ 
		if(c != null){
		//assume false;
//		n = c.next;
		c.next = p;
		p = c;
		c = n;
//		dprint;
		}
		if (c == null){
			c = p;
			p = null;
		}
		n = c.next;
		traverse(c,p,n);
	}
//	dprint;
}

void trav(ref node root)
requires root::ll<> * SENTINEL::node<_,null>
ensures root'::ll<> ;
//& root = SENTINEL;
{
	if (root == null) return;
	else {
		node prev = SENTINEL;
		node curr = root;
		node next = curr.next;
//		dprint;
		traverse(curr,prev,next);
		root = next;
	}
//dprint;
}
