data node {
 int mark;
 node left;
 node right;
}

dag<v:int,s,M> == self=null & M = {} & s!=self
	or self::node<_,l,r> * l::dag<0,s,Ml> U* r::dag<1,s,Mr> & M = union(Ml,Mr,{self}) & s != self & v = 0
	or self::node<_,l,r> * l::dag<1,s,Ml> U* r::dag<0,s,Mr> & M = union(Ml,Mr,{self}) & s != self & v = 1
	inv self!=s
	memE M->(node<@L,@M,@L> & v = 0 ; node<@L,@L,@M> & v != 0);

dagseg<v:int,p,M> == self = p & M = {}
	or self::node<_,l,r> * l::dagseg<0,p,Ml> U* r::dag<1,p,Mr> & M = union(Ml,Mr,{self}) & self != p & v = 0
	or self::node<_,l,r> * l::dag<0,p,Ml> U* r::dagseg<1,p,Mr> & M = union(Ml,Mr,{self}) & self != p & v = 0
	or self::node<_,l,r> * l::dagseg<1,p,Ml> U* r::dag<0,p,Mr> & M = union(Ml,Mr,{self}) & self != p & v = 1
	or self::node<_,l,r> * l::dag<1,p,Ml> U* r::dagseg<0,p,Mr> & M = union(Ml,Mr,{self}) & self != p & v = 1
	inv true
	memE M->(node<@L,@M,@L> & v = 0 ; node<@L,@L,@M> & v != 0);

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::dag<_,sentinel,Mc> * prev::dagseg<_,sentinel,Mp> & cur != null
ensures prev'::dag<_,sentinel,union(Mc,Mp)> & cur'=sentinel;
requires cur::dagseg<_,sentinel,Mc> * prev::dag<_,sentinel,Mp> & cur != sentinel
ensures prev'::dag<_,sentinel,union(Mc,Mp)> & cur'=sentinel;
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

