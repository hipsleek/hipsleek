data node {
  int v;
  node n;
}

pred pub_ll<n> == self=null & n=0 & self<?@Lo
  or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self<?@Lo & v<?@Lo
  inv n>=0;
pred pri_ll<n> == self=null & n=0 & self<?@Hi
  or self::node<v,q> * q::pri_ll<m> & n>0 & m=n-1 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "private->public_fail" self::pri_ll<n> -> self::pub_ll<n>;

node put_sensitive1_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res::node<x,q> * q::pub_ll<n-1> & res <? @Lo & x <? @Lo;
{
  p.v = x;
  return p;
}

node put_sensitive2_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res::node<x,q> * q::pub_ll<n-1> & res <? @Hi & x <? @Hi;
{
  p.v = x;
  return p;
}

node put_sensitive3_fail(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res::node<x,q> * q::pub_ll<n-1> & res <? @Lo & x <? @Lo;
{
  p.v = x;
  return p;
}

node put_sensitive4_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res::node<x,q> * q::pub_ll<n-1> & res <? @Hi & x <? @Hi;
{
  p.v = x;
  return p;
}

node put_sensitiveS_safe(node p, int x)
  requires p::pub_ll<n> & n>0
  ensures res::node<x,q> * q::pub_ll<n-1> & res <? @Lo;
{
  p.v = x;
  return p;
}

int put_get1_1_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node q = put_sensitive1_safe(p, x);
  return q.v;
}

int put_get1_2_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node q = put_sensitive1_safe(p, x);
  return q.v;
}

int put_get1_3_fail(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node q = put_sensitive1_safe(p, x);
  return q.v;
}

int put_get1_4_fail(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node q = put_sensitive1_safe(p, x);
  return q.v;
}

int put_get2_1_fail(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node q = put_sensitive2_safe(p, x);
  return q.v;
}

int put_get2_2_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node q = put_sensitive2_safe(p, x);
  return q.v;
}

int put_get2_3_fail(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node q = put_sensitive2_safe(p, x);
  return q.v;
}

int put_get2_4_fail(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node q = put_sensitive2_safe(p, x);
  return q.v;
}

int put_get3_1_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node q = put_sensitive3_fail(p, x);
  return q.v;
}

int put_get3_2_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node q = put_sensitive3_fail(p, x);
  return q.v;
}

int put_get3_3_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node q = put_sensitive3_fail(p, x);
  return q.v;
}

int put_get3_4_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node q = put_sensitive3_fail(p, x);
  return q.v;
}

int put_get4_1_fail(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node q = put_sensitive4_safe(p, x);
  return q.v;
}

int put_get4_2_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node q = put_sensitive4_safe(p, x);
  return q.v;
}

int put_get4_3_fail(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node q = put_sensitive4_safe(p, x);
  return q.v;
}

int put_get4_4_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node q = put_sensitive4_safe(p, x);
  return q.v;
}

int put_getS_1_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Lo;
{
  node q = put_sensitiveS_safe(p, x);
  return q.v;
}

int put_getS_2_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Lo
  ensures res=x & res <? @Hi;
{
  node q = put_sensitiveS_safe(p, x);
  return q.v;
}

int put_getS_3_fail(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Lo;
{
  node q = put_sensitiveS_safe(p, x);
  return q.v;
}

int put_getS_4_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <? @Hi
  ensures res=x & res <? @Hi;
{
  node q = put_sensitiveS_safe(p, x);
  return q.v;
}

int put_getS_S_safe(node p, int x)
  requires p::pub_ll<n> & n>0
  ensures res=x & res <? x;
{
  node q = put_sensitiveS_safe(p, x);
  return q.v;
}
