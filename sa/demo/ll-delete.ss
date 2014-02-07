data node {
  int val;
  node next;
}


HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node b,node c, node d).

HeapPred H1(node a).
HeapPred H2(node a,node b).
HeapPred HP1(node a, node b).
//HeapPred G1(node a, node b, node c).


ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;

void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;//'

void delete(ref node x)

  infer[H1,G2]
  requires H1(x)
  ensures G2(x,x');//'

/*
  requires x::ll<>
  ensures x::ll<> & x'=null;//';
*/
{
  if (x == null)
    return;
  else {
    node n = x.next ;
    x=null;
    delete(n);
  }
}

