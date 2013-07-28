data node {
 int mark;
 node left;
 node right;
}

dag<s,M> == self=null & M = {} & s!=self
	or self::node<_,l,r> * l::dag<s,Ml> U* r::dag<s,Mr> & M = union(Ml,Mr,{self}) & s != self
	inv self!=s
	memE M->(node<@M,@M,@M>);

dagseg<p,M> == self = p & M = {}
	or self::node<_,l,r> * l::dagseg<p,Ml> U* r::dag<p,Mr> & M = union(Ml,Mr,{self}) & self != p
	or self::node<_,l,r> * l::dag<p,Ml> U* r::dagseg<p,Mr> & M = union(Ml,Mr,{self}) & self != p
	inv true
	memE M->(node<@M,@M,@M>);

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::dag<sentinel,Mc> * prev::dagseg<sentinel,Mp> & cur != null
ensures prev'::dag<sentinel,union(Mc,Mp)> & cur'=sentinel;
requires cur::dagseg<sentinel,Mc> * prev::dag<sentinel,Mp> & cur != sentinel
ensures prev'::dag<sentinel,union(Mc,Mp)> & cur'=sentinel;
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

