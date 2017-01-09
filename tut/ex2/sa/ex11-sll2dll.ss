data node2 {
  int val;
  node2 prev;
  node2 next;
}

sll<> == emp & self=null
  or self::node2<_,_,q>*q::sll<>
  inv true;

dll<pr> == emp & self=null
  or self::node2<_,pr,q>*q::dll<self>
  inv true;

HeapPred P(node2 x, node2@NI y).
PostPred Q(node2 x,node2 y).

void sll2dll(node2 x,node2 prlnk)
/*
  requires x::sll<>
  ensures x::dll<prlnk>;
*/
infer [P,Q]
  requires P(x,prlnk)
  ensures Q(x,prlnk);
{
  if (x==null) return;
  else {
     x.prev = prlnk;
     sll2dll(x.next,x);
  }
}


