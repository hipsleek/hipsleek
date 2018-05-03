data node {
  int  val;
  node nxt;
}

lemma_safe self::safell<n> -> self::unsafell<n>;
lemma_safe self::unsafell<n> -> self::safell<n>;

pred safell<n> == self = null & n = 0 & self <^ @Lo & n <^ @Lo
  or self::node<v,q> * q::safell<n-1> & n > 0 & self <^ @Lo & v <^ @Lo
  inv n >= 0;

pred unsafell<n> == self = null & n = 0 & self <^ @Hi & n <^ @Hi
  or self::node<v,q> * q::unsafell<n-1> & n > 0 & self <^ @Hi & v <^ @Hi
  inv n >= 0;

pred zeroll<n> == self = null & n = 0
  or self::node<v,q> * q::zeroll<n-1> & n > 0 & v <= 0
  inv n >= 0;

pred onell<n> == self = null & n = 0
  or self::node<v,q> * q::zeroll<n-1> & n > 0 & v <= 1
  inv n >= 0;

node id(node x)
  requires x::safell<n> & n > 0
  ensures  res::node<_,_> & true & res <^ @Lo;
{
  return x;
}

node id2(node x)
  requires x::safell<n>
  ensures res::unsafell<n>;
{
  return x;
}
node id_fail(node x)
  requires x::unsafell<n>
  ensures res::safell<n>;
{
  return x;
}

node idx(node x)
  requires x::safell<n> & n > 0
  ensures  res::node<_,_> & true & res <^ @Lo;
{
  int y = x.val;
  //  dprint;
  return x;
}
