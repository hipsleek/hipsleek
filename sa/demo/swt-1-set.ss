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

