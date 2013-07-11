data node {
 int mark;
 node left;
 node right;
}

tree<M> == self=null & M = {}
 or self::node<_,l,r> * l::tree<Ml> * r::tree<Mr> & M = union(Ml,Mr,{self})
 inv true;

treeG<s> == self = null & s != self
	or self::node<_,l,r> * l::treeG<s> * r::treeG<s> & s != self
inv self != s;

treeseg<p> == self=p
    or self::node<_,l,r> * l::treeseg<p> * r::treeG<p> & self != p
    or self::node<_,l,r> * l::treeG<p> * r::treeseg<p> & self != p
inv true;

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::treeG<sentinel> * prev::treeseg<sentinel> & cur != null
ensures prev'::treeG<sentinel> & cur'=sentinel;
requires cur::treeseg<sentinel> * prev::treeG<sentinel> & cur != sentinel
ensures prev'::treeG<sentinel> & cur'=sentinel;
{

  node n,tmp;
  n = cur.left;
  tmp = cur.right;
  // rotate ptrs
  cur.right = prev;
  cur.left = tmp;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sentinel) return;
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sentinel);
//  dprint;
}

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

