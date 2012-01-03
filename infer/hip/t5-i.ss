data node {
  int val;
  node next;
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

int hdtl(ref node x)
 infer [x] 
 requires true
 ensures true; 
{
  x = tl(x);
  return hd(x);
}

node tl(node x)
 infer [x] 
 requires true
 ensures true; 
{
  node t = x.next;
  return t;
}

