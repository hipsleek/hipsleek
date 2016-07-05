data node{
	int val;
	node next;
}

lg<v,"n":s,"s":M> == true&["n","":self = null & self != s; "s": M = {}]
	or self::node<v,nxt> * nxt::lg<v,s,Mn> & ["n","": self != s ;"s": M = union(Mn,{self})]
inv true&["n",""@S:self!=s] ;

ls<v,"n":p,"s":M> == true&["n","":self = p ;"s": M = {}]
	or self::node<v,nxt> * nxt::ls<v,p,Mn> & ["n","":self != p ;"s": M = union(Mn,{self})]
inv true;

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::lg<0,sentinel,Mc> * prev::ls<1,sentinel,Mp> & ["n","": cur != null]
ensures prev'::lg<2,sentinel,M> & ["n": cur'=sentinel; "s": M = union(Mc,Mp)];
requires cur::ls<1,sentinel,Mc> * prev::lg<2,sentinel,Mp> & ["n","": cur != sentinel]
ensures prev'::lg<2,sentinel,M> & ["n": cur'=sentinel; "s": M = union(Mc,Mp)];
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
  if (cur == sentinel) 	return;	
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sentinel);
}

