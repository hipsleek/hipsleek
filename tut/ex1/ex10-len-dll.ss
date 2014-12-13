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

int length(node2 x,node2 prlnk)
  requires x::dll<prlnk>
  ensures x::dll<prlnk> & res>=0;
{
  if (x==null) return 0;
  else {
     node2 tmp = x.prev;
     assert tmp' = prlnk;
     return 1+length(x.next,x);
  }
}


