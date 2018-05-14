data node {
  int v;
  node n;
}

pred pub_ll<n> == self=null & n=0 & self <E @Lo
  or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self <E @Lo & v <E @Lo
  inv n>=0;
pred pri_ll<n> == self=null & n=0 & self <E @Hi
  or self::node<v,q> * q::pri_ll<m> & n>0 & m=n-1 & self <E @Hi & v <E @Hi
  inv n>=0;

lemma_safe "public->private" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "private->public_fail" self::pri_ll<n> -> self::pub_ll<n>;

node upcast(node p)
  requires p::pub_ll<n>
  ensures res::pri_ll<n>;
{
  return p;
}

node downcast_fail(node p)
  requires p::pri_ll<n>
  ensures res::pub_ll<n>;
{
  return p;
}
