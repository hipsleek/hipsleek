data node {
  node next;
}

ll<> == self = null or 
  (exists q: self::node<q> * q::ll<>);

lseg<p> == self = p or 
  (exists q: self::node<q> * q::lseg<p>);

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

