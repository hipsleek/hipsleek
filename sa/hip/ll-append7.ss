data node {
  int val;
  node next;
}


HeapPred G2(node a, node b).
HeapPred G1(node a).
HeapPred G3(node b,node c, node d).

HeapPred H1(node a).
HeapPred H2(node a, node b).
HeapPred HP1(node a, node b).
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

  infer[H1,G2]
  requires H1(x) & y=null
  ensures G2(x,y);//*y::node<a,null>;
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

