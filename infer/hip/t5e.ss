data node {
  int val;
  node next;
}

int hd(node x)
 requires x::node<a,_>@L
 ensures res=a; 

int clearhd(node x)
 requires x::node<a,b>
  ensures x::node<0,b>; 

void hdcl(ref node x)
 infer [x] 
 requires true
 ensures true; 
{
  int v = hd(x);
  clearhd(x);
}
