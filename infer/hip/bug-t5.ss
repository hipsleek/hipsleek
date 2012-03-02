data node {
  int val;
  node next;
}

// TODO : Order of Processing must be based on call hierarchy!

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

int hdtl(ref node x)
 infer [x] 
 requires true
 ensures true; 
{
  x = tl(x);
  return hd(x);
}
