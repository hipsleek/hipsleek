data node {
  int v;
  node n;
}

pred pub_ll<n> == self=null & n=0 & self <E #@Lo
  or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self <E #@Lo & v <E #@Lo
  inv n>=0;
pred pri_ll<n> == self=null & n=0 & self <E #@Hi
  or self::node<v,q> * q::pri_ll<m> & n>0 & m=n-1 & self <E #@Hi & v <E #@Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "private->public_fail" self::pri_ll<n> -> self::pub_ll<n>;

int sum1_safe(node p)
  requires p::pub_ll<n> & p  <E  #@Lo
  ensures res  <E  #@Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum1_safe(p.n);
  }
}

int sum2_safe(node p)
  requires p::pub_ll<n> & p  <E  #@Lo
  ensures res  <E  #@Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum2_safe(p.n);
  }
}

int sum3_fail(node p)
  requires p::pri_ll<n> & p  <E  #@Hi
  ensures res  <E  #@Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum3_fail(p.n);
  }
}

int sum4_safe(node p)
  requires p::pri_ll<n> & p  <E  #@Hi
  ensures res  <E  #@Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.v + sum4_safe(p.n);
  }
}
