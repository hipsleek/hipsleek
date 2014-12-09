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

int length(node x,node prlnk)
  requires x::dll<prlnk>
  ensures x::dll<prlnk> & res>=0;
{
  if (x==null) return 0;
  else {
     assert x.prev = prlnk;
     return 1+length(x.next,x);
  }
}


