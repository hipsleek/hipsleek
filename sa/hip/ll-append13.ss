data node {
  int val;
  node next;
}

HeapPred G1(node a, node b).
HeapPred H1(node a).

/*
ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;
*/

void append(node x, node y)

//G1 can not be a lseg because y!=null
  infer[H1,G1]
  requires H1(x)*y::node<a,null>
     ensures G1(x,y) *y::node<a,null>;


{
  if (x == null)
    x = y;
  else
    append(x.next, y);
}

