data node {
  int x;
  node n;
}
safell<n> == self = null & n = 0 & self <^ @Lo
	or self::node<x, q> * q::safell<n-1> & x = 0 & x <^ @Lo & self <^ @Lo
	inv n >= 0;

unsafell<n> == self = null & n = 0 & self <^ @Hi
	or self::node<x, q> * q::safell<n-1> & x = 0 & x <^ @Hi & self <^ @Hi
	inv n >= 0;

int sumll(node y)
  requires y::safell<n>
  ensures res <^ @Lo;
{
  if (y == null) {
    return 0;
  }
  else {
    return y.x + sumll(y.n);
  }
}

int sumll_unsafe(node y)
  requires y::unsafell<n>
  ensures res <^ @Lo;
{
  if (y == null) {
    return 0;
  }
  else {
    return y.x + sumll(y.n);
  }
}
