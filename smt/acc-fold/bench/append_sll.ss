data node {
  int val;
  node next;
}

ll<> == self=null or self::node<_, q> * q::ll<>;

void append(node x, node y)
  requires x::ll<> * y::ll<> & x != null 
  ensures x::ll<>;

{
  if (x.next != null) {
    append(x.next, y);
    return;
  }
  else {
    x.next = y;
    return;
  }
}

