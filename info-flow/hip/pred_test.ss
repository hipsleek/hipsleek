data node {
  int  val;
  node nxt;
}

lemma_safe self::safell<n> -> self::unsafell<n>;
lemma_safe self::unsafell<n> -> self::safell<n>;
lemma_safe self::zeroll<n> -> self::onell<n>;
lemma_safe self::onell<n> -> self::zeroll<n>;

pred safell<n> == self = null & n = 0 & self <^ @Lo
  or self::node<v,q> * q::safell<n-1> & n > 0 & self <^ @Lo & v <^ @Lo
  inv n >= 0;

pred unsafell<n> == self = null & n = 0 & self <^ @Hi
  or self::node<v,q> * q::unsafell<n-1> & n > 0 & self <^ @Hi & v <^ @Hi
  inv n >= 0;

pred zeroll<n> == self = null & n = 0
  or self::node<v,q> * q::zeroll<n-1> & n > 0 & v <= 0
  inv n >= 0;

pred onell<n> == self = null & n = 0
  or self::node<v,q> * q::zeroll<n-1> & n > 0 & v <= 1
  inv n >= 0;

node id0(node x)
  requires x::safell<n>
  ensures  res::safell<n> & res <^ @Lo;
{
  return x;
  dprint;
}


node id(node x)
  requires x::safell<n> & n > 0
  ensures  res::node<_,_> & true & res <^ @Lo;
{
  return x;
}

node id_fail(node x)
  requires x::unsafell<n> & n > 0
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
node id2_fail(node x)
  requires x::unsafell<n>
  ensures res::safell<n>;
{
  return x;
}

node idx(node x)
  requires x::safell<n> & n > 0
  ensures  res::node<_,_> & res <^ @Lo;
{
  int y = x.val;
  //  dprint;
  return x;
}

int get1(node x)
  requires x::safell<n> & n > 0
  ensures  res <^ @Lo;
{
  int y = x.val;
  //  dprint;
  return y;
}

int get1_fail(node x)
  requires x::unsafell<n> & n > 0
  ensures  res <^ @Lo;
{
  int y = x.val;
  //  dprint;
  return y;
}

int get2a(node x)
  requires x::safell<n> & n > 0
  ensures  res <^ @Hi;
{
  int y = x.val;
  //  dprint;
  return y;
}

int get2b(node x)
  requires x::unsafell<n> & n > 0
  ensures  res <^ @Hi;
{
  int y = x.val;
  //  dprint;
  return y;
}
