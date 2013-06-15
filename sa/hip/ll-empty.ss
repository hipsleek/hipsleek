data node {
  int val;
  node next;
}

HeapPred G1(node a).
HeapPred H1(node a).

bool empty(node x)
  infer[H1,G1]
  requires H1(x)
     ensures G1(x) & res | !res;
  /* requires x::ll1<> */
  /* case { */
  /*   x = null -> ensures EMPT1(res);//res */
  /*   x != null -> ensures EMPT2(res);//!(res) */
  /* } */
{
  if (x == null)
    return true;
  else
    return false;
}
