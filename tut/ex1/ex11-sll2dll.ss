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

void sll2dll(node2 x,node2 prlnk)
  requires x::sll<>
  ensures x::dll<prlnk>;
{
  if (x==null) return;
  else {
     x.prev = prlnk;
     sll2dll(x.next,x);
  }
}


