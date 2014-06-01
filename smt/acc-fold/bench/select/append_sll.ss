data node {
  node next;
}

ll<> == self=null or 
  (exists q: self::node<q> * q::ll<>);

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

