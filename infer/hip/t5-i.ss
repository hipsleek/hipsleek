data node {
  int val;
  node next;
}

int hdtl(ref node x)
 infer [x] 
 requires true
 ensures true; 
{
  x = tl(x);
  return hd(x);
}

int hd(node x)
 infer [x] 
 requires true
 ensures true; 
/*
   requires x::node<inf1,inf2>
   ensures res=inf1;
*/
{
  return x.val;
}

node tl(node x)
 infer [x] 
 requires true
 ensures true; 
{
  node t = x.next;
  return t;
}

