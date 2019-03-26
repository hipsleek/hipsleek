data node {
  int val;
  node next;
}

ll<n> == self=null & n = 0
  or self::node<_, r> * r::ll<n2> & n = 1 + n2;

int length(node x)
  requires x::ll<n>
  ensures x::ll<n> & res = n;
{
  if (x == null) return 0;
  else {
    // int k;
    // k = 3 + length(x.next);
    // return k;
    return 3 + length(x.next);
  }
}
