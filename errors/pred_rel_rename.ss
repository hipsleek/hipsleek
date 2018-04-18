data node {
  int v;
  node n;
}
relation nodeR(node s).
pred ll<n> == self=null & n=0 & nodeR(self)
           or self::node<_,q> * q::ll<n-1> & nodeR(self)
          inv n>=0 & nodeR(self);
node foo(node p)
  requires p::ll<n> & n>0
  ensures  res::node<_,_> & nodeR(res);
{
  return p;
}
