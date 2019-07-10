data node {
  node next;
}

ll<n> == self=null & n = 0
  or self::node<r> * r::ll<n2> & n = 1 + n2;

int length(node x)
  requires x::ll<n>
  ensures x::ll<n> & res = n;
{
  if (x == null)
      return 5;
  else
      return 1 + length(x.next);
}
