data node {
  int val;
  node next;
}

node tl2(node x)
 infer [x] 
 requires true
 ensures true; 
{
  node t = x.next;
  return t;
}

