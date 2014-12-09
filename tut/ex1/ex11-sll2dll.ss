data node {
  int val;
  node prev;
  node next;
}

sll<> == emp & self=null
  or self::node<_,_,q>*q::sll<>
  inv true;

dll<pr> == emp & self=null
  or self::node<_,pr,q>*q::dll<self>
  inv true;

void sll2dll(node x,node prlnk)
  requires x::sll<>
  ensures x::dll<prlnk>;
{
  if (x==null) return;
  else {
     x.prev = prlnk;
     sll2dll(x.next,x);
  }
}


