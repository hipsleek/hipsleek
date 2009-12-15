data node {
  int val;
  node next;
}

bigint<v> == self = null & v = 0 or
             self::node<p, q> * q::bigint<v1> & 0 <= p & p <= 9 & v = 10*v1 + p
             inv v >= 0;

int int_value(node x)
  requires x::bigint<v>
  ensures res = v;
{
  if (x == null) return 0;
  return x.val + int_value(x.next)*10;
}

node add_one_digit(node x, int c)
  requires x::bigint<v> & c >= 0 & c <= 9
  ensures res::bigint<v+c> * x::bigint<v>;
{
  if (x == null) {
    return new node(c, x);
  } else {
    int t = x.val + c;
    int carry = 0;
    if (t >= 10) {
      t = t - 10;
      carry = 1;
    }
    node rest = add_one_digit(x.next, carry);
    return new node(t, rest);
  }
}

node add_c(node x, node y, int c)
  requires x::bigint<v1> * y::bigint<v2> & 0 <= c <= 9
  ensures res::bigint<v1+v2+c> * x::bigint<v1> * y::bigint<v2>;
{
  if (x == null) {
    if (y == null) {
      if (c == 0) return null;
      else return new node(c, null);
    } else {
      return add_one_digit(y, c);
    }
  } else {
    if (y == null) {
      return add_one_digit(x, c);
    } else {
      int t = x.val + y.val + c;
      int carry = 0;
      if (t >= 10) {
        carry = t/10;
        t = t - carry*10;
      }
      node rest = add_c(x.next, y.next, carry);
      return new node(t, rest);
    }
  }
}

node add(node x, node y)
  requires x::bigint<v1> * y::bigint<v2>
  ensures res::bigint<v1+v2> * x::bigint<v1> * y::bigint<v2>;
{
  return add_c(x, y, 0);
}

int mod2(int a, int b) case {
  a >= 0 -> case {
    b >= 1 -> requires true ensures a = b*q + res & q >= 0 & 0 <= res <= b-1;
    b <= -1 -> requires true ensures a = b*q + res & q <= 0 & 0 <= res <= -b-1;
    -1 < b < 1 -> requires false ensures false;
  }
  a < 0 -> case {
    b >= 1 -> requires true ensures a = b*q + res & q <= -1 & 0 <= res <= b-1;
    b <= -1 -> requires true ensures a = b*q + res & q >= 1 & 0 <= res <= -b-1;
    -1 < b < 1 -> requires false ensures false;
  }
}

int mod3(int a, int b)
  requires b = 10
  ensures a = 10*q + res & q >= 0 & 0 <= res <= 9;

int div_with_remainder(int a, int b, ref int r)
  requires a >= 0 & b >= 1
  ensures a = b*res + r' & res >= 0 & 0 <= r' <= b-1;

node mult_c(node x, int d, int c)
  requires x::bigint<v> & 0<=c & c<=9 & 0<=d & d<=9 
  ensures res::bigint<v*d+c> * x::bigint<v>;
{
  if (x == null) {
    if (c == 0) return null;
    else return new node(c, null);
  } else {
    int ans = x.val * d + c;
    int carry = 0;
    if (ans >= 10) {
      carry = div_with_remainder(ans, 10, ans);
      //carry = ans/10;
      //ans = ans - carry*10;
      //ans = ans%10;
    }
    node rest = mult_c(x.next, d, carry);
    return new node(ans, rest);
  }
}

/* left shift all digits one pos (multiplied by ten) */
node shift_left(node x)
  requires x::bigint<v>
  ensures res::bigint<v*10>;
{
  if (x == null) {
    return x;
  } else {
    return new node(0, x);
  }
}

node mult(node x, node y)
  requires x::bigint<v1> * y::bigint<v2>
  ensures res::bigint<v1*v2> * x::bigint<v1> * y::bigint<v2>;
{
  if (x == null || y == null) {
    return null;
  } else {
    node t1 = mult_c(x, y.val, 0);
    node t2 = shift_left(mult(x, y.next));
    return add_c(t1, t2, 0);
  }
}

bool is_zero(node x)
  requires x::bigint<v>
  ensures res & v = 0 or !res & v != 0;
{
  if (x == null) return true;
  if (x.val == 0 && is_zero(x.next)) return true;
  return false;
}
