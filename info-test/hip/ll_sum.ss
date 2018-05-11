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

lemma_safe "public->private" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "private->public_fail" self::pri_ll<n> -> self::pub_ll<n>;

int sum1(node p)
  requires p::pub_ll<n> & p <? @Lo
  ensures res <? @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum1(p.n);
  }
}

int sum2(node p)
  requires p::pub_ll<n> & p <? @Lo
  ensures res <? @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum2(p.n);
  }
}

int sum3_fail(node p)
  requires p::pri_ll<n> & p <? @Hi
  ensures res <? @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum3_fail(p.n);
  }
}

int sum4(node p)
  requires p::pri_ll<n> & p <? @Hi
  ensures res <? @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum4(p.n);
  }
}
