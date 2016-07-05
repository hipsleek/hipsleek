data node {
 int mark;
 node left;
 node right;
}

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

