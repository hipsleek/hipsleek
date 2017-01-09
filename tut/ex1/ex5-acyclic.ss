data node {
  int val;
  node next;
}

ll<> == emp & self=null
  or self::node<_,q>*q::ll<>
  inv true;

int length(node x)
  requires x::ll<>
  ensures x::ll<>;
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

