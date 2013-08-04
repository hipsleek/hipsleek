data node {
 int mark;
 node left;
 node right;
}

tree<s,v> == self=null & s != self
	or self::node<v,l,r> * l::tree<s,v> * r::tree<s,v> & s != self
inv self != s;

treeseg<p,v,w> == self=p
	or self::node<v,l,r> * l::treeseg<p,v,w> * r::tree<p,w> & self != p
	or self::node<v,l,r> * l::tree<p,w> * r::treeseg<p,v,w> & self != p
inv true;

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::tree<sentinel,0> * prev::treeseg<sentinel,1,0> & cur != null
ensures prev'::tree<sentinel,2> & cur'=sentinel;
requires cur::treeseg<sentinel,1,0> * prev::tree<sentinel,2> & cur != sentinel
ensures prev'::tree<sentinel,2> & cur'=sentinel;
{

  node n,tmp;
  n = cur.left;
  tmp = cur.right;
  // mark node
  cur.mark++;
//dprint;
  // rotate ptrs
  cur.right = prev;
  cur.left = tmp;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sentinel){
assume false;
	 return; }
  if (cur == null) {
assume false;
      // change direction;
      cur = prev;
      prev = null;
  }
dprint;
  lscan(cur,prev,sentinel);
}
