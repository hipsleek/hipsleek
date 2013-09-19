data node {
 int mark;
 node left;
 node right;
}

tree<v,s> == self=null & s != self
	or self::node<v,l,r> * l::tree<v,s> * r::tree<v,s> & s !=self
inv self != s;

treeseg<v,p> == self=p 
	or self::node<v,l,r> * l::treeseg<v,p> * r::tree<v,p> & self != p
	or self::node<v,l,r> * l::tree<v,p> * r::treeseg<v,p> & self != p
inv true;

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::tree<0,sentinel> * prev::treeseg<1,sentinel> & cur != null
ensures prev'::tree<2,sentinel> & cur'=sentinel;
requires cur::treeseg<1,sentinel> * prev::tree<2,sentinel> & cur != sentinel
ensures prev'::tree<2,sentinel> & cur'=sentinel;
{

  node n,tmp;
  n = cur.left;
  tmp = cur.right;
  //mark node
  cur.mark++;
  // rotate ptrs
  cur.right = prev;
  cur.left = tmp;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sentinel){
	 return; }
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
dprint;
  lscan(cur,prev,sentinel);
}

