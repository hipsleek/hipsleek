data node {
 int mark;
 node left;
 node right;
}

tree<s,M> == self=null & M = {} & s != self
 or self::node<v,l,r> * l::tree<s,Ml> * r::tree<s,Mr> 
& M = union(Ml,Mr,{self}) 
& s !=self
//inv forall(x: x notin M | (x != null & x != s)) & self != s;
inv self != s;

treeseg<p,M> == self=p & M = {}
or self::node<v,l,r> * l::treeseg<p,Ml> * r::tree<p,Mr> 
& M = union(Ml,Mr,{self}) 
& self != p
or self::node<v,l,r> * l::tree<p,Ml> * r::treeseg<p,Mr> 
& M = union(Ml,Mr,{self}) 
& self != p
inv true;

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::tree<sentinel,Mc> * prev::treeseg<sentinel,Mp> & cur != null
ensures prev'::tree<sentinel,union(Mc,Mp)> & cur'=sentinel;
requires cur::treeseg<sentinel,Mc> * prev::tree<sentinel,Mp> & cur != sentinel
ensures prev'::tree<sentinel,union(Mc,Mp)> & cur'=sentinel;
{

  node n,tmp;
  n = cur.left;
  tmp = cur.right;
  // rotate ptrs
  cur.right = null;
  cur.right = prev;
  cur.left = null;
  cur.left = tmp;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sentinel){
//	assume false;
	 return; }
  if (cur == null) {
//	assume false;
      // change direction;
      cur = prev;
      prev = null;
  }
//dprint;
  lscan(cur,prev,sentinel);
//  dprint;
}

/*
data node {
 int mark;
 node left;
 node right;
}

treeG<s,B> == self = null & s != self & B={}
  or self::node<v,l,r> * l::treeG<s,B1> * r::treeG<s,B2> & s != self
  &  B=union({v},B1,B2)
inv self != s;

treeseg<p,B> == self=p & B={}
  or self::node<v,l,r> * l::treeseg<p,B1> * r::treeG<p,B2> 
        & self != p & B=union({v},B1,B2)
  or self::node<v,l,r> * l::treeG<p,B1> * r::treeseg<p,B2> & self != p
        & B=union({v},B1,B2)
inv true;

void lscan(ref node cur, ref node prev, node sentinel)
  requires cur::treeG<sentinel,B1> * prev::treeseg<sentinel,B2> & cur != null
ensures prev'::treeG<sentinel,union(B1,B2)> & cur'=sentinel;
requires cur::treeseg<sentinel,B1> * prev::treeG<sentinel,B2> & cur != sentinel
ensures prev'::treeG<sentinel,union(B1,B2)> & cur'=sentinel;
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

infer[H,G]
requires H(t) * H(p)
ensures G(t,2) * G(p,2);

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
*/
