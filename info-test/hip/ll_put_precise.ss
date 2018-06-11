data node {
  int v;
  node n;
}

pred pub_ll<n> == self=null & n=0 & self<?@Lo
  or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self<?@Lo & v<?@Lo
  inv n>=0;
pred fpri_ll<n> == self=null & n=0 & self<?@Hi
  or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self<?@Hi & v<?@Hi
  inv n>=0;
pred pri_ll<n> == self=null & n=0 & self<?@Hi
  or self::node<v,q> * q::pri_ll<m> & n>0 & m=n-1 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "public->first_private_safe" self::pub_ll<n> -> self::fpri_ll<n>;
lemma_safe "first_private->public_fail" self::fpri_ll<n> -> self::pub_ll<n>;
lemma_safe "public->private_safe" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "private->public_fail" self::pri_ll<n> -> self::pub_ll<n>;
lemma_safe "private->first_private_fail" self::pri_ll<n> -> self::fpri_ll<n>;
lemma_safe "first_private->private_safe" self::fpri_ll<n> -> self::pri_ll<n>;

node put_precise1_safe(node p, int x)
  requires p::pub_ll<n> & n>1 & x <? @Lo
  ensures res::pub_ll<n> & res <? @Lo;
{
  p.v = x;
  return p;
}

node put_precise2_safe(node p, int x)
  requires p::pub_ll<n> & n>1 & x <? @Lo
  ensures res::fpri_ll<n> & res <? @Hi;
{
  p.v = x;
  return p;
}

node put_precise3_fail(node p, int x)
  requires p::fpri_ll<n> & n>1 & x <? @Hi
  ensures res::pub_ll<n> & res <? @Lo;
{
  p.v = x;
  return p;
}

node put_precise4_safe(node p, int x)
  requires p::fpri_ll<n> & n>1 & x <? @Hi
  ensures res::fpri_ll<n> & res <? @Hi;
{
  p.v = x;
  return p;
}

node put_preciseS_safe(node p, int x)
  requires p::pub_ll<n> & n>1
  ensures res::fpri_ll<n>;
{
  p.v = x;
  return p;
}

node strip_precise1_safe(node p)
  requires p::pub_ll<n> & n>0
  ensures res::pub_ll<n-1>;
{
  return p.n;
}

node strip_precise2_safe(node p)
  requires p::fpri_ll<n> & n>0
  ensures res::pub_ll<n-1>;
{
  return p.n;
}

node strip_precise3_fail(node p)
  requires p::pri_ll<n> & n>0
  ensures res::pub_ll<n-1>;
{
  return p.n;
}

node strip_precise4_safe(node p)
  requires p::pub_ll<n> & n>0
  ensures res::fpri_ll<n-1>;
{
  return p.n;
}

node strip_precise5_safe(node p)
  requires p::fpri_ll<n> & n>0
  ensures res::fpri_ll<n-1>;
{
  return p.n;
}

node strip_precise6_fail(node p)
  requires p::pri_ll<n> & n>0
  ensures res::fpri_ll<n-1>;
{
  return p.n;
}

node strip_precise7_safe(node p)
  requires p::pub_ll<n> & n>0
  ensures res::pri_ll<n-1>;
{
  return p.n;
}

node strip_precise8_safe(node p)
  requires p::fpri_ll<n> & n>0
  ensures res::pri_ll<n-1>;
{
  return p.n;
}

node strip_precise9_safe(node p)
  requires p::pri_ll<n> & n>0
  ensures res::pri_ll<n-1>;
{
  return p.n;
}
