data node {
  int val;
  node next;
}

ll<> == self=null or self::node<_, q> * q::ll<>;

lseg<p> == self=p or self::node<_, q> * q::lseg<p>;

void append(node x, node y)
  requires x::ll<> & x!=null
  ensures x::lseg<y>;

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

