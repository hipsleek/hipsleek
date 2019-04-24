data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2;

int length(node x)
  requires x::ls<null,n>
  ensures x::ls<null,n> & res = n;
{
  if (x == null) return 0;
  else {
    int k;
    k = 2 + length(x.next);
    return k;
  }
}
