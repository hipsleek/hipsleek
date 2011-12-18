data node {
  int val;
  node next;
}

int hd1(node x)
 infer [x] 
 requires true
 ensures true; //'
/*
   requires x::node<inf1,inf2>
   ensures res=inf1;
*/
{
  int v = x.val;
  //dprint;
  return v;
}

