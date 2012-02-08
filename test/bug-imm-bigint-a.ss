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
  requires x::bigint<v>@L
  ensures true & (res & v = 0 | !res & v != 0);
{
  if (x == null) return true;
  if (x.val == 0 && is_zero(x.next)) return true;
  return false;
}



int compare(node x, node y)

  requires x::bigint<v1> * y::bigint<v2>
  ensures x::bigint<v1> * y::bigint<v2> & 
  (res = 0 & v1 = v2 | res = 1 & v1 > v2 | res = -1 & v1 < v2);
/*
  requires (x::bigint<v1>@L & y::bigint<v2>@L)
  ensures true & (res = 0 & v1 = v2 | res = 1 & v1 > v2 | res = -1 & v1 < v2);
  requires x::bigint<v1>@L * y::bigint<v2>@L
  ensures true & (res = 0 & v1 = v2 | res = 1 & v1 > v2 | res = -1 & v1 < v2);
*/
{
  if (x == null) {
    if (is_zero(y)) return 0;
    return -1;
  }
  if (y == null) {
    if (is_zero(x)) return 0;
    return 1;
  }
  int c = compare(x.next, y.next);
  if (c == 0) return compare_int(x.val, y.val);
  return c;
}


int compare_int(int x, int y)
  requires true
  ensures res = 0 & x = y or res = 1 & x > y or res = -1 & x < y;
//  requires true
//  ensures true & (res = 0 & x = y | res = 1 & x > y | res = -1 & x < y);
{
  if (x == y) return 0;
  if (x > y) return 1;
  return -1;
}

