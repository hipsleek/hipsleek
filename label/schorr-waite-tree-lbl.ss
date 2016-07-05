data node {
 int mark;
 node left;
 node right;
}

tree<"n":s,"s":M> == true&["n": self=null & s != self; "s": M = {}]
 or self::node<_,l,r> * l::tree<s,Ml> * r::tree<s,Mr> & ["s": M = union(Ml,Mr,{self}) ; "n":s !=self]
inv true&["n":self != s];

treeseg<"n":p,"s":M> == true&["n":self=p ; "s": M = {}]
or self::node<_,l,r> * l::treeseg<p,Ml> * r::tree<p,Mr> & ["s": M = union(Ml,Mr,{self}) ; "n":self != p]
or self::node<_,l,r> * l::tree<p,Ml> * r::treeseg<p,Mr> & ["s": M = union(Ml,Mr,{self}) ; "n":self != p]
inv true;

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::tree<sentinel,Mc> * prev::treeseg<sentinel,Mp> & ["n": cur != null]
ensures prev'::tree<sentinel,M> & ["n": cur'=sentinel ; "s": M = union(Mc,Mp)];
requires cur::treeseg<sentinel,Mc> * prev::tree<sentinel,Mp> & ["n": cur != sentinel]
ensures prev'::tree<sentinel,M> & ["n": cur'=sentinel ; "s": M = union(Mc,Mp)];
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
