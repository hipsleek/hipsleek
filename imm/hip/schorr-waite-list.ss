data node{
	int val;
	node next;
}

lg<s,M,a1,a2> == self = null & M = {} & self != s
  or self::node<_@a1,nxt@a2> * nxt::lg<s,Mnxt,a1,a2> & M = union(Mnxt,{$ self}) & self != s
  inv self!=s;

ls<p,M,a1,a2> == self = p & M = {} //& self!=null
  or self::node<_@a1,nxt@a2> * nxt::ls<p,M1,a1,a2> & self != p & M = union({$ self},M1) 
  inv true;


void lscan(ref node cur, ref node prev, node sentinel)
  requires cur::lg<sentinel,Mc,@A,@M> * prev::ls<sentinel,Mp,@A,@M> & cur != null
  ensures prev'::lg<sentinel,union(Mc,Mp),@A,@M> & cur'=sentinel;
  requires cur::ls<sentinel,Mc,@A,@M> * prev::lg<sentinel,Mp,@A,@M> & cur != sentinel
  ensures prev'::lg<sentinel,union(Mc,Mp),@A,@M> & cur'=sentinel;
{

  node n;
  n = cur.next;
  // rotate ptrs
  cur.next = prev;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sentinel) 	return;	
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sentinel);
//dprint;
}

