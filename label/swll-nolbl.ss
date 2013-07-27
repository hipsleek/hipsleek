data node{
	int val;
	node next;
}

/*
ll<M> == self = null & M = {}
	or self::node<_,nxt> * nxt::ll<Mnxt> & M = union(Mnxt,{self})
inv forall(x: x notin M | x != null);
*/

lg<s,M> == self = null & self != s & M = {} 
	or self::node<_,nxt> * nxt::lg<s,Mnxt> & M = union(Mnxt,{self}) & self != s
//inv forall(x: x notin M | (x != null & x != s));
inv self!=s;

ls<p,M> == true & ["n":self = p; "s":M = {}]
	or self::node<_,nxt> * nxt::ls<p,M1> & ["n": self != p ; "s": M = union({self},M1)]
inv true;

global node SENTINEL;

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::lg<sentinel,Mc> * prev::ls<sentinel,Mp> & ["n": cur != null]
ensures prev'::lg<sentinel,M> & ["n": cur'=sentinel; "s": M = union(Mc,Mp)];
requires cur::ls<sentinel,Mc> * prev::lg<sentinel,Mp> & ["n": cur != sentinel]
ensures prev'::lg<sentinel,M> & ["n": cur'=sentinel; "s": M = union(Mc,Mp)];
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

