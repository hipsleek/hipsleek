data node2 {
  int val;
  node2 prev;
  node2 next;
}

dll<pr, sum> == emp & self=null & sum = 0
  or self::node2<val, pr,q>*q::dll<self, sum2> & sum = sum2 + val;

int sum(node2 x)
  requires x::dll<prlnk, n>
  ensures res = n;
{

  if (x==null) return 0;
  else {
     int k;
     k = sum(x.next);
     return x.val - k;
  }
}