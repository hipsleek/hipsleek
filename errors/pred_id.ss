data node {
  int v;
  node n;
}

lemma_safe self::ll0<n> -> self::ll1<n>.

// LL with all values <= 0
pred ll0<n> == self=null & n=0
            or self::node<v,q> * q::ll0<n-1> & v<=0
           inv n>=0;
// LL with all values <= 1
pred ll1<n> == self=null & n=0
            or self::node<v,q> * q::ll1<n-1> & v<=1
           inv n>=0;

node id(node p)
  requires p::ll0<n>
  ensures  res::ll1<n>;
{
  return p;
}
