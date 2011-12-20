data node {
  int val;
  node next;
}


int hd0(ref node x)
 infer [x] 
 requires true
 ensures true; //'
/*
   requires x::node<inf1,inf2>
   ensures res=inf1;
*/
{
  x = x.next;
  return x.val;
}

