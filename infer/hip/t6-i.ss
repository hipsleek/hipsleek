data node {
  int val;
  node next;
}

int hd(node x)
 requires x::node<a,_>@L
 ensures res=a; 
{
  return x.val;
}

node tl(node x)
 requires x::node<_,b>@L
 ensures res=b; 
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
