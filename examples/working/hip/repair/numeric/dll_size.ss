data node2 {
  int val;
  node2 prev;
  node2 next;
}

dll<pr, size> == emp & self=null & size = 0
  or self::node2<_,pr,q>*q::dll<self, size2> & size = size2 + 1;

// int length(node2 x)
//   requires x::dll<prlnk, n>
//   ensures res = n;
// {

//   if (x==null) return 2;
//   else {
//      return 1 + length(x.next);
//   }
// }

int length(node2 x,node2 prlnk)
  requires x::dll<prlnk, n>
  ensures res = n;
{
  if (x==null) return 2;
  else {
     node2 tmp = x.prev;
     assert tmp' = prlnk;
     return 1 + length(x.next,x);
  }
}

int length(node2 x,node2 prlnk)
  requires x::dll<prlnk, n>
  ensures res = n;
{
  if (x==null) return 2;
  else {
     return 1 + length(x.next,x);
  }
}
