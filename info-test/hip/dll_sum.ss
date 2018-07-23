data node {
  int v;
  node n;
  node p;
}

pred pub_dll<n,p> == self=null & n=0 & self<?@Lo
  or self::node<v,q,p> * q::pub_dll<m,p> & n>0 & m=n-1 & self<?@Lo & v<?@Lo
  inv n>=0;
pred pri_dll<n,p> == self=null & n=0 & self<?@Hi
  or self::node<v,q,p> * q::pri_dll<m,p> & n>0 & m=n-1 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_dll<n,p> -> self::pri_dll<n,p>;
lemma_safe "private->public_fail" self::pri_dll<n,p> -> self::pub_dll<n,p>;

int sum1_safe(node p)
  requires p::pub_dll<n,null> & p <? @Lo
  ensures res <? @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum1_safe(p.n);
  }
}

int sum2_safe(node p)
  requires p::pub_dll<n,null> & p <? @Lo
  ensures res <? @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum2_safe(p.n);
  }
}

int sum3_fail(node p)
  requires p::pri_dll<n,null> & p <? @Hi
  ensures res <? @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum3_fail(p.n);
  }
}

int sum4_safe(node p)
  requires p::pri_dll<n,null> & p <? @Hi
  ensures res <? @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum4_safe(p.n);
  }
}
