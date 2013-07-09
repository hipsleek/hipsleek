data node {
 int mark;
 node left;
 node right;
}

tree<M> == self=null & M = {}
 or self::node<_,l,r> * l::tree<Ml> * r::tree<Mr> & M = union(Ml,Mr,{self})
 inv true;

void traverse(ref node c,ref node p)
requires c::tree<Mc> * p::tree<Mp>
ensures p'::tree<M> & M = union(Mc,Mp) & c' = null;
/*
infer[H,G]
requires H(t) * H(p)
ensures G(t,2) * G(p,2);
*/
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
requires root::tree<M>
ensures root'::tree<M>;
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

