data node{
	int val;
	node next;
}

ls<M,p> == self=p & M={}
  or self::node<_,nxt> * nxt::ls<M2,p> & self=p & M=union(M2,{self})
inv true;


void lscan(ref node cur, ref node prev, node sentinel)
  requires cur::ls<M1,null> * prev::ls<M2,sentinel> * sentinel::node<_,_>@L & cur!=null
  ensures prev'::ls<M3,null> & cur'=sentinel & M3=union(M1,M2);
requires cur::ls<M1,sentinel> * prev::ls<M2,null> * sentinel::node<_,_>@L & cur!=sentinel
ensures prev'::ls<M3,null> & cur'=sentinel  & M3=union(M1,M2);
{

  node n;
  n = cur.next;
  // rotate ptrs
  cur.next = prev;
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

