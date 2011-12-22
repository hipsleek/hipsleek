data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

int hd(node x)
 infer [x] 
  requires true
 ensures true; 
/*
   requires x::node<inf1,in>
   ensures res=inf1;
*/
{
  return x.val;
}



node tl(node x)
 infer [x] 
  requires x::ll<n>
 ensures true; 
{
  node t = x.next;
  return t;
}

/*
int hdtl(ref node x)
 infer [x] 
 requires true
 ensures true; 
{
  x = tl(x);
  return hd(x);
}
*/
