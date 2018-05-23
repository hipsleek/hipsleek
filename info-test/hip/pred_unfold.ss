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

node unfold1_safe(node p)
  requires p::pub_ll<n> & n>0
  ensures res::node<v,_> & v<?@Lo & res<?@Lo;
{
  return p;
}

node unfold2_safe(node p)
  requires p::pub_ll<n> & n>0
  ensures res::node<v,_> & v<?@Hi & res<?@Hi;
{
  return p;
}

node unfold3_fail(node p)
  requires p::pri_ll<n> & n>0
  ensures res::node<v,_> & v<?@Lo & res<?@Lo;
{
  return p;
}

node unfold4_safe(node p)
  requires p::pri_ll<n> & n>0
  ensures res::node<v,_> & v<?@Hi & res<?@Hi;
{
  return p;
}

node double_unfold1_safe(node p)
  requires p::pub_ll<n> & n>0
  ensures res::node<v,q> * q::pub_ll<n-1> & v<?@Lo & res<?@Lo & q<?@Lo;
{
  return p;
}

node double_unfold2_safe(node p)
  requires p::pub_ll<n> & n>0
  ensures res::node<v,q> * q::pri_ll<n-1> & v<?@Hi & res<?@Hi & q<?@Hi;
{
  return p;
}

node double_unfold3_fail(node p)
  requires p::pri_ll<n> & n>0
  ensures res::node<v,q> * q::pub_ll<n-1> & v<?@Lo & res<?@Lo & q<?@Lo;
{
  return p;
}

node double_unfold4_safe(node p)
  requires p::pri_ll<n> & n>0
  ensures res::node<v,q> * q::pri_ll<n-1> & v<?@Hi & res<?@Hi & q<?@Hi;
{
  return p;
}
