data node {
  int val;
  node next;
}

ll<n> == self=null & n = 0
  or self::node<_, r> * r::ll<n2> & n = 1 + n2 & n > 0
  inv n >= 0;

node copy(node x)
requires x::ll<n>
ensures res::ll<n> * x::ll<n>;
{
  if (x == null) return x;
  else {
      node tmp;
      tmp = copy(x.next.next);
      // tmp = copy(x.next);
      return new node(x.val, tmp);
  }
}
