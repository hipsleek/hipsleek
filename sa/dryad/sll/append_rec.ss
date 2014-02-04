data node {
  int val;
  node next;
}


HeapPred G2(node a, node b).
HeapPred H2(node a,node b).

ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;

void append(node x, node y)
  infer[H2,G2]
  requires H2(x,y)
  ensures G2(x,y);
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}
