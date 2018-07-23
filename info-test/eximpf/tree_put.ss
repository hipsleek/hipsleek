data node {
  int v;
  node l;
  node r;
  node p;
}

pred pub_tree<n,p> == self=null & n=0 & self <E @Lo
  or self::node<v,l,r,p> * l::pub_tree<ln,self> * r::pub_tree<rn,self>
     & n>0 & n=ln+rn+1 & self <E @Lo & v <E @Lo
  inv n>=0;
pred pri_tree<n,p> == self=null & n=0 & self <E @Hi
  or self::node<v,l,r,p> * l::pri_tree<ln,self> * r::pri_tree<rn,self>
     & n>0 & n=ln+rn+1 & self <E @Hi & v <E @Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_tree<n,p> -> self::pri_tree<n,p>;
lemma_safe "private->public_fail" self::pri_tree<n,p> -> self::pub_tree<n,p>;

node put1_safe(node t, int x)
  requires t::pub_tree<n,p> & n>0 & x <E @Lo
  ensures res::pub_tree<n,p> & res <E @Lo;
{
  t.v = x;
  return t;
}

node put2_safe(node t, int x)
  requires t::pub_tree<n,p> & n>0 & x <E @Lo
  ensures res::pri_tree<n,p> & res <E @Hi;
{
  t.v = x;
  return t;
}

node put3_fail(node t, int x)
  requires t::pri_tree<n,p> & n>0 & x <E @Hi
  ensures res::pub_tree<n,p> & res <E @Lo;
{
  t.v = x;
  return t;
}

node put4_safe(node t, int x)
  requires t::pri_tree<n,p> & n>0 & x <E @Hi
  ensures res::pri_tree<n,p> & res <E @Hi;
{
  t.v = x;
  return t;
}
