data node {
  int val;
  node next;
}


HeapPred G2(node a, node b).
HeapPred H1(node a).

ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;
ll1<p> == self=null & p=null
  or self::node<_,q>*q::ll1<_> & p=null
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;

void delete(node@R x)

  infer[H1,G2]
  requires H1(x)
  ensures G2(x,x');//'


  /* requires x::ll<> */
  /* ensures x::ll<> & x'=null;//'; */
  /* requires x::ll<> */
  /* ensures x::ll1<x'>;//'; */

{
  if (x == null)
    return;
  else {
    node n = x.next ;
    x=null;
    delete(n);
  }
  /* while (x) */
  /*   infer[H1,G2] */
  /* requires H1(x) */
  /* ensures G2(x,x'); */
  /*    *\/ */
  /*   /\* */
  /*     requires x::ll<> */
  /*     ensures x::ll<> & x'=null;//'; */
  /*   *\/ */
  /*   { */
  /*   struct node* tmp = x ; */
  /*   x=x->next; */
  /*   tmp = NULL; */
  /* } */
  /* return; */
}

