data node {
  int val;
  node next;
}
             
bigint<b, v> == self = null & v = 0 or
                 self::node<p, q> * q::bigint<b, v1> & 0 <= p < b & v = b*v1 + p & v > 0
                 inv v >= 0;

int int_value_of(node x, int b)
  requires x::bigint<b, v>
  ensures res = v;
{
  if (x == null) return 0;
  return x.val + int_value_of(x.next, b)*b;
}

node bigint_of(int v, int b)
  requires v >= 0 & 0 < b <= 10
  ensures res::bigint<b, v>;
{
  if (v == 0) return null;
  if (v < b) {
    return new node(v, null);
  } else {
    int digit = 0;
    int rem = div_with_remainder(v, b, digit);
    node rest = bigint_of(rem, b);
    return new node(digit, rest);
  }
}

node add_one_digit(node x, int c, int b)
  requires x::bigint<b, v> & 0 <= c < b & b <= 10
  ensures res::bigint<b, v+c> * x::bigint<b, v>;
{
  if (x == null) {
    if (c == 0) return null;
    return new node(c, x);
  } else {
    int t = x.val + c;
    int carry = 0;
    if (t >= b) {
      t = t - b;
      carry = 1;
    }
    node rest = add_one_digit(x.next, carry, b);
    return new node(t, rest);
  }
}

node add_c(node x, node y, int c, int b)
  requires x::bigint<b, v1> * y::bigint<b, v2> & 0 <= c < b & b <= 10
  ensures res::bigint<b, v1+v2+c> * x::bigint<b, v1> * y::bigint<b, v2>;
{
  if (x == null) {
    if (y == null) {
      if (c == 0) return null;
      else return new node(c, null);
    } else {
      return add_one_digit(y, c, b);
    }
  } else {
    if (y == null) {
      return add_one_digit(x, c, b);
    } else {
      int t = x.val + y.val + c;
      int carry = 0;
      if (t >= b) {
        carry = div_with_remainder(t, b, t);
        // carry = t/b;
        // t = t - carry*b;
      }
      node rest = add_c(x.next, y.next, carry, b);
      return new node(t, rest);
    }
  }
}

node add(node x, node y, int b)
  requires x::bigint<b, v1> * y::bigint<b, v2> & 0 < b <= 10
  ensures res::bigint<b, v1+v2> * x::bigint<b, v1> * y::bigint<b, v2>;
{
  return add_c(x, y, 0, b);
}

node mult_c(node x, int d, int c, int b)
  requires x::bigint<b, v> & 0 <= c < b & 0 <= d < b & b <= 10
  ensures res::bigint<b, v*d+c> * x::bigint<b, v>;
{
  if (x == null || d == 0) {
    if (c == 0) return null;
    return new node(c, null);
  } else {
    int ans = x.val * d + c;
    int carry = 0;
    if (ans >= b) {
      carry = div_with_remainder(ans, b, ans);
      // carry = ans/b;
      // ans = ans - carry*b;
      // ans = ans%10;
    }
    node rest = mult_c(x.next, d, carry, b);
    return new node(ans, rest);
  }
}

node shift_left(node x, int b)
  requires x::bigint<b, v>
  ensures res::bigint<b, v*b>;
{
  if (x== null) {
    return x;
  } else {
    return new node(0, x);
  }
}

node mult(node x, node y, int b)
  requires x::bigint<b, v1> * y::bigint<b, v2> & 0 < b <= 10
  ensures res::bigint<b, v1*v2> * x::bigint<b, v1> * y::bigint<b, v2>;
{
  if (x == null || y == null) {
    return null;
  } else {
    node t1 = mult_c(x, y.val, 0, b);
    node t2 = shift_left(mult(x, y.next, b), b);
    return add_c(t1, t2, 0, b);
  }
}

int compare(node x, node y)
  requires x::bigint<b, v1> * y::bigint<b, v2>
  ensures res = 0 & v1 = v2 or res > 0 & v1 > v2 or res < 0 & v1 < v2;
{
  if (x == null) {
    if (y == null) return 0;
    return -1;
  }
  if (y == null) {
    return 1;
  }
  int c = compare(x.next, y.next);
  if (c == 0) return compare_int(x.val, y.val);
  return c;
}

bool is_equal(node x, node y)
  requires x::bigint<b, v1> * y::bigint<b, v2>
  ensures res & v1 = v2 or !res & v1 != v2;
{
  if (x == null || y == null) {
    return x == null && y == null;
  } else {
    bool eq = is_equal(x.next, y.next);
    if (x.val == y.val) return eq;
    else return false;
  }
}

bool is_zero(node x)
  requires x::bigint<b, v>
  ensures res & v = 0 or !res & v != 0;
{
  if (x == null) return true;
  return false;
}

int compare_int(int x, int y)
  requires true
  ensures res = 0 & x = y or res = 1 & x > y or res = -1 & x < y;
{
  if (x == y) return 0;
  if (x > y) return 1;
  return -1;
}

int div_with_remainder(int a, int b, ref int r)
  requires a >= 0 & b >= 1
  ensures a = b*res + r' & res >= 0 & 0 <= r' <= b-1;
{
  int result = a/b;
  r = a - b * result;
  return result;
}
