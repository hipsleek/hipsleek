data node {
  int v;
  node l;
  node r;
  node p;
}

pred pub_tree<n,p> == self=null & n=0 & self <? @Lo
  or self::node<v,l,r,p> * l::pub_tree<ln,self> * r::pub_tree<rn,self>
  & n>0 & n=ln+rn+1 & self <? @Lo & v <? @Lo
  inv n>=0;
pred pri_tree<n,p> == self=null & n=0 & self <? @Hi
  or self::node<v,l,r,p> * l::pri_tree<ln,self> * r::pri_tree<rn,self>
  & n>0 & n=ln+rn+1 & self <? @Hi & v <? @Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_tree<n,p> -> self::pri_tree<n,p>;
lemma_safe "private->public_fail" self::pri_tree<n,p> -> self::pub_tree<n,p>;

node put_sensitive1_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res::node<x,l,r,_> * r::pub_tree<n1,_> * l::pub_tree<n2,_> & n=n1+n2+1 & res <? @Lo & x <? @Lo;
{
  t.v = x;
  return t;
}

node put_sensitive2_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res::node<x,l,r,_> * r::pub_tree<n1,_> * l::pub_tree<n2,_> & n=n1+n2+1 & res <? @Hi & x <? @Hi;
{
  t.v = x;
  return t;
}

node put_sensitive3_fail(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res::node<x,l,r,_> * r::pub_tree<n1,_> * l::pub_tree<n2,_> & n=n1+n2+1 & res <? @Lo & x <? @Lo;
{
  t.v = x;
  return t;
}

node put_sensitive4_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res::node<x,l,r,_> * r::pub_tree<n1,_> * l::pub_tree<n2,_> & n=n1+n2+1 & res <? @Hi & x <? @Hi;
{
  t.v = x;
  return t;
}

node put_sensitiveS_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0
  ensures res::node<x,l,r,_> * r::pub_tree<n1,_> * l::pub_tree<n2,_> & n=n1+n2+1 & res <? @Lo;
{
  t.v = x;
  return t;
}

int put_get1_1_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node l = put_sensitive1_safe(t, x);
  return l.v;
}

int put_get1_2_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node l = put_sensitive1_safe(t, x);
  return l.v;
}

int put_get1_3_fail(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node l = put_sensitive1_safe(t, x);
  return l.v;
}

int put_get1_4_fail(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node l = put_sensitive1_safe(t, x);
  return l.v;
}

int put_get2_1_fail(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node l = put_sensitive2_safe(t, x);
  return l.v;
}

int put_get2_2_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node l = put_sensitive2_safe(t, x);
  return l.v;
}

int put_get2_3_fail(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node l = put_sensitive2_safe(t, x);
  return l.v;
}

int put_get2_4_fail(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node l = put_sensitive2_safe(t, x);
  return l.v;
}

int put_get3_1_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node l = put_sensitive3_fail(t, x);
  return l.v;
}

int put_get3_2_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node l = put_sensitive3_fail(t, x);
  return l.v;
}

int put_get3_3_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node l = put_sensitive3_fail(t, x);
  return l.v;
}

int put_get3_4_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node l = put_sensitive3_fail(t, x);
  return l.v;
}

int put_get4_1_fail(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node l = put_sensitive4_safe(t, x);
  return l.v;
}

int put_get4_2_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node l = put_sensitive4_safe(t, x);
  return l.v;
}

int put_get4_3_fail(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node l = put_sensitive4_safe(t, x);
  return l.v;
}

int put_get4_4_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node l = put_sensitive4_safe(t, x);
  return l.v;
}

int put_getS_1_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node l = put_sensitiveS_safe(t, x);
  return l.v;
}

int put_getS_2_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node l = put_sensitiveS_safe(t, x);
  return l.v;
}

int put_getS_3_fail(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node l = put_sensitiveS_safe(t, x);
  return l.v;
}

int put_getS_4_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node l = put_sensitiveS_safe(t, x);
  return l.v;
}

int put_getS_S_safe(node t, int x)
  requires t::pub_tree<n,_> & n>0
  ensures res=x & res <? x;
{
  node l = put_sensitiveS_safe(t, x);
  return l.v;
}
