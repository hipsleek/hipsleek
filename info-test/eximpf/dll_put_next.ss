data node {
  int v;
  node n;
  node p;
}

pred pub_dll<n,p> == self=null & n=0 & self <E @Lo
  or self::node<v,q,p> * q::pub_dll<m,self> & n>0 & m=n-1 & self <E @Lo & v <E @Lo
  inv n>=0;
pred pri_dll<n,p> == self=null & n=0 & self <E @Hi
  or self::node<v,q,p> * q::pri_dll<m,self> & n>0 & m=n-1 & self <E @Hi & v <E @Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_dll<n,p> -> self::pri_dll<n,p>;
lemma_safe "private->public_fail" self::pri_dll<n,p> -> self::pub_dll<n,p>;

node put_next1_safe(node p, int x)
  requires p::pub_dll<n,_> & n>1 & x <E @Lo
  ensures res::pub_dll<n,_> & res <E @Lo;
{
  p.n.v = x;
  return p;
}

node put_next2_safe(node p, int x)
  requires p::pub_dll<n,_> & n>1 & x <E @Lo
  ensures res::pri_dll<n,_> & res <E @Hi;
{
  p.n.v = x;
  return p;
}

node put_next3_fail(node p, int x)
  requires p::pri_dll<n,_> & n>1 & x <E @Hi
  ensures res::pub_dll<n,_> & res <E @Lo;
{
  p.n.v = x;
  return p;
}

node put_next4_safe(node p, int x)
  requires p::pri_dll<n,_> & n>1 & x <E @Hi
  ensures res::pri_dll<n,_> & res <E @Hi;
{
  p.n.v = x;
  return p;
}

node put_nextS1_fail(node p, int x)
  requires p::pri_dll<n,_> & n>1
  ensures res::pri_dll<n,_> & res <E @Lo;
{
  p.n.v = x;
  return p;
}

node put_nextS2_safe(node p, int x)
  requires p::pri_dll<n,_> & n>1
  ensures res::pri_dll<n,_> & res <E @Hi;
{
  p.n.v = x;
  return p;
}
