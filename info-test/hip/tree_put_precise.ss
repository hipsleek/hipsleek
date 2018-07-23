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
pred fpri_tree<n,p> == self=null & n=0 & self <? @Hi
  or self::node<v,l,r,p> * l::pub_tree<ln,self> * r::pub_tree<rn,self>
  & n>0 & n=ln+rn+1 & self <? @Hi & v <? @Hi
  inv n>=0;
pred pri_tree<n,p> == self=null & n=0 & self <? @Hi
  or self::node<v,l,r,p> * l::pri_tree<ln,self> * r::pri_tree<rn,self>
  & n>0 & n=ln+rn+1 & self <? @Hi & v <? @Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_tree<n,p> -> self::pri_tree<n,p>;
lemma_safe "private->public_fail" self::pri_tree<n,p> -> self::pub_tree<n,p>;
lemma_safe "first_private->public_fail" self::fpri_tree<n,p> -> self::pub_tree<n,p>;
lemma_safe "public->first_private_safe" self::pub_tree<n,p> -> self::fpri_tree<n,p>;
lemma_safe "first_private->private_safe" self::fpri_tree<n,p> -> self::pri_tree<n,p>;
lemma_safe "private->first_private_fail" self::pri_tree<n,p> -> self::fpri_tree<n,p>;

node put_precise1_safe(node t, int x)
  requires t::pub_tree<n,_> & n>1 & x <? @Lo
  ensures res::pub_tree<n,_> & res <? @Lo;
{
  t.v = x;
  return t;
}

node put_precise2_safe(node t, int x)
  requires t::pub_tree<n,_> & n>1 & x <? @Lo
  ensures res::fpri_tree<n,_> & res <? @Hi;
{
  t.v = x;
  return t;
}

node put_precise3_fail(node t, int x)
  requires t::fpri_tree<n,_> & n>1 & x <? @Hi
  ensures res::pub_tree<n,_> & res <? @Lo;
{
  t.v = x;
  return t;
}

node put_precise4_safe(node t, int x)
  requires t::fpri_tree<n,_> & n>1 & x <? @Hi
  ensures res::fpri_tree<n,_> & res <? @Hi;
{
  t.v = x;
  return t;
}

node put_preciseS_safe(node t, int x)
  requires t::pub_tree<n,_> & n>1
  ensures res::fpri_tree<n,_>;
{
  t.v = x;
  return t;
}
