data node{
	int val;
	node next;
}

/*
ll<M> == self = null & M = {}
	or self::node<_,nxt> * nxt::ll<Mnxt> & M = union(Mnxt,{self})
inv forall(x: x notin M | x != null);
*/

lg<s,M> == self = null & M = {} & self != s
	or self::node<_,nxt> * nxt::lg<s,Mnxt> & M = union(Mnxt,{self}) & self != s
//inv forall(x: x notin M | (x != null & x != s));
inv self!=s 
& (self=null & M={} | self!=null & M!={})
;

ls<p,M> == self = p & M = {} //& self!=null
	or self::node<_,nxt> * nxt::ls<p,M1> & self != p & M = union({self},M1) 
  inv true
  & (self=p & M={} | self!=p & M!={} & self!=null)
  ;
//self!=null;

//global node SENTINEL;

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::lg<sentinel,Mc> * prev::ls<sentinel,Mp> & cur != null
ensures prev'::lg<sentinel,union(Mc,Mp)> & cur'=sentinel;
requires cur::ls<sentinel,Mc> * prev::lg<sentinel,Mp> & cur != sentinel
ensures prev'::lg<sentinel,union(Mc,Mp)> & cur'=sentinel;
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

