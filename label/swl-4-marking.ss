data node{
	int val;
	node next;
}

lx<v,g,s> == self=g & self!=s & v = 2
  or self::node<v,nxt> * nxt::lx<v,g,s> & self!=g & self!=s
  inv self!=s  ;

void lscan(ref node cur, ref node prev, node sent)
requires cur::lx<vc,a,b> * prev::lx<vp,b,a> & cur!=a & (a=null & b=sent & vc = 0  & vp = 1 | a=sent & b=null & vc = 1 & vp = 2)
ensures prev'::lx<2,null,sent>  & cur'=sent ;
{

  node n;
  n = cur.next;
  //mark node
  cur.val++;
  // rotate ptrs
  cur.next = prev;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sent) {
      //assume false;
      return;
  }
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
      //dprint;
  }
  lscan(cur,prev,sent);
}

