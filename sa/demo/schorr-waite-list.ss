data node{
	int val;
	node next;
}

/*
ll<M> == self = null & M = {}
	or self::node<_,nxt> * nxt::ll<Mnxt> & M = union(Mnxt,{self})
inv true;
*/

global node SENTINEL;

ls<p> == self=p
    or self::node<_,nxt> * nxt::ls<p> & self!=p
inv true;

ll1<s> == self = null & self != s
	or self::node<_,p> * p::ll1<s> & self != s
inv self!= s;

void lscan(ref node cur, ref node prev, node sentinel)
/*
requires cur::ls<null> * prev::ls<sentinel> * sentinel::node<_,_>@L & cur!=null
ensures prev'::ls<null> & cur'=sentinel;
requires cur::ls<sentinel> * prev::ls<null> * sentinel::node<_,_>@L & cur!=sentinel
ensures prev'::ls<null> & cur'=sentinel;
*/
requires cur::ll1<sentinel> * prev::ls<sentinel> & cur!=null
ensures prev'::ll1<sentinel> & cur'=sentinel;
requires cur::ls<sentinel> * prev::ll1<sentinel> & cur!=sentinel
ensures prev'::ll1<sentinel> & cur'=sentinel;
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
  //dprint;
}

void traverse(ref node c, ref node p)
requires c::ll<Mc> * p::ll<Mp>
ensures p'::ll<M> & M = union(Mc,Mp) & c' = null;
{
if(c == null) return;
else {
	node n = c.next;
	c.next = p;
	p = c;
	c = n;
	traverse(c,p);
	}
}

void trav(ref node root)
requires root::ll<M>
ensures root'::ll<M>;
//& root = SENTINEL;
{
	if (root == null) return;
	else {
		node prev = null;
		node curr = root;
//		dprint;
		traverse(curr,prev);
		curr = prev;
		prev = null;
		traverse(curr,prev);
		root = prev;
	}
//dprint;
}

void scan(ref node cur, ref node prev)
requires cur::ll<Mc> * prev::ll<Mp>
ensures prev'::ll<M1> * cur'::ll<M2> & union(M1,M2) = union(Mp,Mc);
{
  node n;
  if (cur != SENTINEL && cur != null) 
  {
  	n = cur.next;
	cur.next = prev;
	prev = cur;
	cur = n;
	if (cur == null) {
		cur = prev;
		prev = null;
	}
	scan(cur,prev);
  }  
}

void scantrav(ref node root)
requires root::ll<M> * SENTINEL::node<_,null>
case{
	root != null -> ensures root'::ll<M1>;
	root = null -> ensures root'::ll<M> & root' = root;
}
{
  node cur,prev;
  if (root == null) return;
  prev = SENTINEL;
  cur = root;
  scan(cur,prev);
  root = prev;
//  dprint;
}

/*

ls<p> == self = p &
	or self::node<_,nxt> * nxt::ls<p> 
inv true;

void scan(ref node cur, ref node prev, node sentinel)
requires cur::ls<null> * prev::ls<sentinel> * sentinel::node<_,_>@L
ensures prev'::ls<null> * cur'=sentinel;
requires cur::ls<sentinel> * prev::ls<null> * sentinel::node<_,_>@L
ensures prev'::ls<null> * cur'=sentinel;
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
  };
  scan(cur,prev);
}
  if (cur != SENTINEL && cur != null) 
  {
  	n = cur.next;
	cur.next = prev;
	prev = cur;
	cur = n;
	if (cur == null) {
		cur = prev;
		prev = null;
	}
	scan(cur,prev);
  }  
}
*/
