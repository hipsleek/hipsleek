 data node {
  int val;
  node next;
 }

HeapPred G2(node a, node b).
HeapPred H1(node a).


void delete(node x)
/*
  requires x::ll<>
  ensures x::ll<>;
*/
{
  while (x != null) [while_del]
   infer[H1,G2] requires H1(x)  ensures G2(x,x');//'
    /*
      requires x::ll<>
      ensures x::ll<> & x'=null;//'
    */
  {
    node tmp = x;
    x=x.next;
    tmp = null;
  }
  return;
}


