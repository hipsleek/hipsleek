data node2 {
  int val;
  node2 prev;
  node2 next;
}

dll<pr, n> == emp & self=null & n = 0
  or self::node2<_, pr,q>*q::dll<self, n2> & n = n2 + 1;

int length(node2 x)
  requires x::dll<prlnk, n>
  ensures res = n;
{

  if (x==null) return 0;
  else {
     return 1 + 5 * length(x.next);
  }
}
