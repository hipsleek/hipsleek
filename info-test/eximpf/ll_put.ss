data node {
  int v;
  node n;
}

pred pub_ll<n> == self=null & n=0 & self<E#@Lo
  or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self<E#@Lo & v<E#@Lo
  inv n>=0;
pred pri_ll<n> == self=null & n=0 & self<E#@Hi
  or self::node<v,q> * q::pri_ll<m> & n>0 & m=n-1 & self<E#@Hi & v<E#@Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "private->public_fail" self::pri_ll<n> -> self::pub_ll<n>;

node put1_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <E #@Lo
  ensures res::pub_ll<n> & res <E #@Lo;
{
  p.v = x;
  return p;
}

node put2_safe(node p, int x)
  requires p::pub_ll<n> & n>0 & x <E #@Lo
  ensures res::pri_ll<n> & res <E #@Hi;
{
  p.v = x;
  return p;
}

node put3_fail(node p, int x)
  requires p::pri_ll<n> & n>0 & x <E #@Hi
  ensures res::pub_ll<n> & res <E #@Lo;
{
  p.v = x;
  return p;
}

node put4_safe(node p, int x)
  requires p::pri_ll<n> & n>0 & x <E #@Hi
  ensures res::pri_ll<n> & res <E #@Hi;
{
  p.v = x;
  return p;
}
