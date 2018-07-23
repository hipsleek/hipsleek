data node {
  int v;
  node n;
  node p;
}

pred pub_dll<n,p> == self=null & n=0 & self <? @Lo
  or self::node<v,q,p> * q::pub_dll<m,self> & n>0 & m=n-1 & self <? @Lo & v <? @Lo
  inv n>=0;
pred pri_dll<n,p> == self=null & n=0 & self <? @Hi
  or self::node<v,q,p> * q::pri_dll<m,self> & n>0 & m=n-1 & self <? @Hi & v <? @Hi
  inv n>=0;

lemma_safe "public->private" self::pub_dll<n,p> -> self::pri_dll<n,p>;
lemma_safe "private->public_fail" self::pri_dll<n,p> -> self::pub_dll<n,p>;

node put_prev1_safe(node p, int x)
  requires p::pub_dll<n,q> * q::node<_,p,_> & n>1 & x <? @Lo
  ensures res::pub_dll<n,q> * q::node<_,p,_> & res <? @Lo;
{
  p.p.v = x;
  return p;
}

node put_prev2_safe(node p, int x)
  requires p::pub_dll<n,q> * q::node<_,p,_> & n>1 & x <? @Lo
  ensures res::pri_dll<n,q> * q::node<_,p,_> & res <? @Hi;
{
  p.p.v = x;
  return p;
}

node put_prev3_fail(node p, int x)
  requires p::pri_dll<n,q> * q::node<_,p,_> & n>1 & x <? @Hi
  ensures res::pub_dll<n,q> * q::node<_,p,_> & res <? @Lo;
{
  p.p.v = x;
  return p;
}

node put_prev4_safe(node p, int x)
  requires p::pri_dll<n,q> * q::node<_,p,_> & n>1 & x <? @Hi
  ensures res::pri_dll<n,q> * q::node<_,p,_> & res <? @Hi;
{
  p.p.v = x;
  return p;
}

node put_prevS1_fail(node p, int x)
  requires p::pri_dll<n,q> * q::node<_,p,_> & n>1
  ensures res::pri_dll<n,q> * q::node<_,p,_> & res <? @Lo;
{
  p.p.v = x;
  return p;
}

node put_prevS2_safe(node p, int x)
  requires p::pri_dll<n,q> * q::node<_,p,_> & n>1
  ensures res::pri_dll<n,q> * q::node<_,p,_> & res <? @Hi;
{
  p.p.v = x;
  return p;
}
