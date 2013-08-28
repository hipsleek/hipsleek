
data node{
    node next;
}

HeapPred H(node a).

void foo(node x)
infer[H] 
  requires H(x) 
  ensures true;// res
{
  node tmp;
  if (x==null) {
    tmp=x.next;
  } else {
    tmp=x.next;
  }
}

/*

*/
