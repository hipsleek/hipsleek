//xisa
data node {
  int val;
  node prev;
  node next;
}

HeapPred H1(node a).
HeapPred H2(node a).
  HeapPred H3(node a, node@NI b).
HeapPred G1(node a).

node reverse (node y, node p)
  infer[H1,H2,G1]
//  requires H1(y)* H2(p)
  requires H3(y, p)
     ensures G1(res);
{
  //y=x;
  //x=null;
 if (y != null) {
   node z = y;
   y = reverse (y.next, z);
    if (y !=null)
     y.next = p;
    // if (p != null)
    // p.prev = r;
   //x=z;
 } else {
   y = p;
   // if (p != null)
   //  p.prev = null;
 }
 return y;
}

