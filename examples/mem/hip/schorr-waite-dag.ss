data node {
 int mark;
 node left;
 node right;
}

dag<M> == self=null & M = {}
	or self::node<_,l,r> * l::dag<Ml> U* r::dag<Mr> & M = union(Ml,Mr,{self})
	inv true
	memE M->();

void traverse(ref node c,ref node p)
requires c::dag<Mc> * p::dag<Mp>
ensures p'::dag<M> & M = union(Mc,Mp) & c' = null;

{ 
  if (c == null) return;
  else {
  	node n = c.left;
 	node tmp = c.right;
	c.right = p;
	c.left = tmp;
	p = c;
	c = n;
	traverse(c,p);
  }
}

void trav(ref node root)
requires root::dag<M>
ensures root'::dag<M>;
{
	if (root == null) return;
	else {
		node prev = null;
		node curr = root;
		traverse(curr,prev);
		curr = prev;
		prev = null;
		traverse(curr,prev);
		root = prev;
	}
}

