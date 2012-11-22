data node {
  int val;
  node next;
}

bigint<v> == self = null & v = 0 or
     self::node<p, q> * q::bigint<v1> & 0 <= p <= 9 & v = 10*v1 + p 
             inv v >= 0;

bool is_zero(node x)
  requires x::bigint<v>
  ensures x::bigint<v> & (res & v = 0 | !res & v != 0);

bool is_equal(node x, node y)
  requires x::bigint<v1> * y::bigint<v2>
  ensures x::bigint<v1> * y::bigint<v2> & (res & v1 = v2 | !res & v1 != v2);
{
  if (x == null) {
    if (is_zero(y)) return true;
    else return false;
  } else {
    if (y == null) {
      if (is_zero(x)) return true;
      else return false;
    } else {
      if (x.val == y.val) return is_equal(x.next, y.next);
      else return false;
    }
  }
  // return compare(x, y) == 0;
}


