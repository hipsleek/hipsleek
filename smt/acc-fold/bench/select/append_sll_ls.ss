data node {
  node next;
}

ll<> == self=null or 
  (exists v, q: self::node<v, q> * q::ll<>);

lseg<p> == self=p or 
  (exists v, q: self::node<v, q> * q::lseg<p>);

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

