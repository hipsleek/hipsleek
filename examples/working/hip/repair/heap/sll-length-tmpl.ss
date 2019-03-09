data node {
  int val;
  node next;
}

HeapPred P().
HeapPred Q().

ll<n> == self=null & n = 0
  or self::node<_, r> * r::ll<n2> & n = 1 + n2;

int fcode()
  requires P()
  ensures Q();

int length(node x)
  requires x::ll<n>
  ensures x::ll<n> & res = n;
{
  if (x == null) return fcode();
  else {
    int k;
    k = 1 + length(x.next);
    return k;
  }
}
