data node {
 int mark;
 node left;
 node right;
}

/*
tree<s> == self=null & s != self
	 or self::node<_,l,r> * l::tree<s> * r::tree<s> & s !=self
inv self != s;

treeseg<p> == self = p 
	or self::node<_,l,r> * l::treeseg<p> * r::tree<p> & self != p
	or self::node<_,l,r> * l::tree<p> * r::treeseg<p> & self != p
inv true;
*/

tx<n,g,s> == self = g & self != s & n != s
	or self::node<_,l,r> * l::tx<n,g,s> * r::tx<n,n,s> & self != g & self != s & n != s
	or self::node<_,l,r> * l::tx<n,n,s> * r::tx<n,g,s> & self != g & self != s & n != s
inv self != s & n != s;

/*
treeseg<s> = tx<null,s,null>

tree<s> = tx<null,null,s>

requires cur::tree<sentinel> * prev::treeseg<sentinel> & cur != null
ensures prev'::tree<sentinel> & cur'=sentinel;
requires cur::treeseg<sentinel> * prev::tree<sentinel> & cur != sentinel
ensures prev'::tree<sentinel> & cur'=sentinel;

cur::tx<null,null,sentinel> * prev::tx<null,sentinel,null> & cur != null
cur::tx<null,sentinel,null> * prev::tx<null,null,sentinel> & cur != sentinel

= cur::tx<null,a,b> * prev::tx<null,b,a> & cur != a & (a=null & b=sentinel | a=sentinel & b=null)

prev'::tx<null,null,sentinel & cur' = sentinel

lx<g,s> == self=g & self!=s 
  or self::node<_,nxt> * nxt::lx<g,s> & self!=g & self!=s inv self!=s;
*/

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::tx<null,a,b> * prev::tx<null,b,a> & cur != a & 
        (a=null & b=sentinel | a=sentinel & b=null)
ensures prev'::tx<null,null,sentinel>  & cur' = sentinel; 
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
}

