data node {
	int val;
	node next;
}

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

HeapPred D(node a).
HeapPred E(node a, node b).

void delete_list(ref node x)
  infer[D,E]
  requires D(x)
  ensures E(x,x');//'
{
  if (x!=null) {
     dispose(x);
  }
}
