data node {
 int mark;
 int swing;
 node left;
 node right;
}

HeapPred H(node a).
HeapPred G(node a,int x).

tree<v> == self=null
 or self::node<0,_,p,q> * p::tree<0> * q::tree<0> & v = 0
 or self::node<0,_,p,q> * p::tree<_> * q::tree<_> & v = 1
 or self::node<1,_,p,q> * p::tree<2> * q::tree<2> & v = 2
 inv true;

treeG<> == self=null or self::node<_,_,l,r> * l::treeG<> * r::treeG<>;

global node SENTINEL;

void traverse(node root)
requires root::treeG<> * SENTINEL::node<_,_,null,null>
ensures root::treeG<> * SENTINEL::node<_,_,null,null>;
/*
infer[H,G]
requires H(t) * H(p)
ensures G(t,2) * G(p,2);
*/
{ 
  node prev,cur,next,tmp;
  if (root == null) return;
  prev = SENTINEL;
  cur = root;
  while (cur != SENTINEL) 
  requires cur::node<_,_,l,r> * l::treeG<> * r::treeG<> * prev::node<_,_,_,_>
  ensures cur::node<_,_,r,prev> * l::treeG<> * r::treeG<> * prev::node<_,_,_,_> & cur' = l;
  {
  	next = cur.left;
 	tmp = cur.right;
	cur.right = null;
	cur.right = prev;
	cur.left = null;
	cur.left = tmp;
	prev = cur;
	cur = next;
	if (cur == null) {
		cur = prev;
		prev = null;
	}
  }
}
