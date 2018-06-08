data node {
  int v;
  node n;
}

pred pub_ll<n> == self=null & n=0 & self<?#@Lo
  or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self<?#@Lo & v<?#@Lo
  inv n>=0;
pred pri_ll<n> == self=null & n=0 & self<?#@Hi
  or self::node<v,q> * q::pri_ll<m> & n>0 & m=n-1 & self<?#@Hi & v<?#@Hi
  inv n>=0;

node id1(node p)
  requires p::pub_ll<n>
  ensures res<?#@Lo;
{
  return p;
}

node id2(node p)
  requires p::pub_ll<n>
  ensures res<?#@Hi;
{
  return p;
}

node id3_fail(node p)
  requires p::pri_ll<n>
  ensures res<?#@Lo;
{
  return p;
}

node id4(node p)
  requires p::pri_ll<n>
  ensures res<?#@Hi;
{
  return p;
}
