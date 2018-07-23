data node {
  int v;
  node n;
  node p;
}

pred pub_dll<n,p> == self=null & n=0 & self <E @Lo
  or self::node<v,q,p> * q::pub_dll<m,self> & n>0 & m=n-1 & self <E @Lo & v <E @Lo
  inv n>=0;
pred fpri_dll<n,p> == self=null & n=0 & self <E @Hi
  or self::node<v,q,p> * q::pub_dll<m,self> & n>0 & m=n-1 & self <E @Hi & v <E @Hi
  inv n>=0;
pred pri_dll<n,p> == self=null & n=0 & self <E @Hi
  or self::node<v,q,p> * q::pri_dll<m,self> & n>0 & m=n-1 & self <E @Hi & v <E @Hi
  inv n>=0;

lemma_safe "dll__public->dll__first_private_safe" self::pub_dll<n,p> -> self::fpri_dll<n,p>;
lemma_safe "dll__first_private->dll__public_fail" self::fpri_dll<n,p> -> self::pub_dll<n,p>;
lemma_safe "dll__public->dll__private_safe" self::pub_dll<n,p> -> self::pri_dll<n,p>;
lemma_safe "dll__private->dll__public_fail" self::pri_dll<n,p> -> self::pub_dll<n,p>;
lemma_safe "dll__private->dll__first_private_fail" self::pri_dll<n,p> -> self::fpri_dll<n,p>;
lemma_safe "dll__first_private->dll__private_safe" self::fpri_dll<n,p> -> self::pri_dll<n,p>;

node put_precise1_safe(node p, int x)
  requires p::pub_dll<n,null> & n>1 & x <? @Lo
  ensures res::pub_dll<n,null> & res <? @Lo;
{
  p.v = x;
  return p;
}

node put_precise2_safe(node p, int x)
  requires p::pub_dll<n,null> & n>1 & x <? @Lo
  ensures res::fpri_dll<n,null> & res <? @Hi;
{
  p.v = x;
  return p;
}

node put_precise3_fail(node p, int x)
  requires p::fpri_dll<n,null> & n>1 & x <? @Hi
  ensures res::pub_dll<n,null> & res <? @Lo;
{
  p.v = x;
  return p;
}

node put_precise4_safe(node p, int x)
  requires p::fpri_dll<n,null> & n>1 & x <? @Hi
  ensures res::fpri_dll<n,null> & res <? @Hi;
{
  p.v = x;
  return p;
}

node put_preciseS_safe(node p, int x)
  requires p::pub_dll<n,null> & n>1
  ensures res::fpri_dll<n,null>;
{
  p.v = x;
  return p;
}
