 data node {
  int val;
  node next;
 }

HeapPred G1(node a, node b).
HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G2(node a).

void delete(node x)
   infer[H2,G2] requires H2(x)  ensures G2(x);
/*
  requires x::ll<>
  ensures x::ll<>;
*/
{
  while (x != null) [whiledel]
   infer[H1,G1] requires H1(x)  ensures G1(x,x');//'
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


