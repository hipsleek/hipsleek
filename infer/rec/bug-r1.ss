data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

int length(node x)
  requires x::ll<n>@L
  ensures res=n;
{
  if (x==null) {
    int r=0;
    dprint;
    return r;
  }
  else {
    assume false;
    int m = length(x.next);
    return 1+m;
  }
}
