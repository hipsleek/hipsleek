
/* build a list with only 1s and finally a 0 (arbitrary length) */
data node {
 int val;
 node next;
}

lseg<p, n, S> == self=p & n=0 & S={}
 or self::node<v, r> * r::lseg<p, n-1, S1> & S=union(S1, {v});

void create(ref node x, int n)
//requires x!=null & n >= 0
 requires x::node<_,_> & n >= 0
 ensures x'::lseg<r, n+1, S> * r::node<0,null> //'
  & forall (b : (b notin S | b=77));
{ 
  assert x!=null;
  x.val = 77;
  node t = new node(0,null);
  assert t!=null;
  x.next = t;
  if (n==0) 
  {
   return;
 }
 else
 { 
  bind x to (xval, xnext) in
  {
  create(xnext,n-1);
 }
}
}

