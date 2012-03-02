data node {
  int val;
  node next;
}

bigint<v> == self = null & v = 0 or
     self::node<p, q> * q::bigint<v1> & 0 <= p <= 9 & v = 10*v1 + p & v>0
     inv v >= 0;

node clone(node x)
  requires x::bigint<v>
  ensures x::bigint<v> * res::bigint<v>;
{
  if (x == null) return x;
  return new node(x.val, clone(x.next));
}

int int_value(node x)
  requires x::bigint<v>
  ensures res = v;
{
  if (x == null) return 0;
  return x.val + int_value(x.next)*10;
}

node add_node(int t,node b)
  requires b::bigint<v> & 0<=t<=9
  ensures res::bigint<v*10+t>;
{
  if (b==null && t==0) return null;
  else return new node(t,b);
}

node bigint_of(int v)
  requires v >= 0
  ensures res::bigint<v>;
{
  if (v < 10) 
    if (v==0) return null;
    else return new node(v,null);
   // return add_node(v, null);
  int digit = 0;
  int rem = div_with_remainder(v, 10, digit);
  node rest = bigint_of(rem);
  return add_node(digit, rest);
}

node add_one_digit(node x, int c)
  requires x::bigint<v> & 0 <= c <= 9
  ensures res::bigint<v+c> * x::bigint<v>;
{
  if (x == null) 
    if (c==0) return null;
    else return new node(c, x);
  int t = x.val + c;
  if (t >= 10) return new node(t - 10, add_one_digit(x.next, 1));
  return new node(t, clone(x.next));
}

node add_c(node x, node y, int c)
  requires x::bigint<v1> * y::bigint<v2> & 0 <= c <= 1
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
        // carry = div_with_remainder(t, 10, t);
        // carry = t/10;
        // t = t - carry*10;
        carry = 1;
        t = t - 10;
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

node sub_one_digit(node x, int c)
  requires x::bigint<v> & 0 <= c <= 9 & c <= v
  ensures res::bigint<v-c> * x::bigint<v>;
{
  if (x == null) return null;
  if (x.val >= c) return add_node(x.val - c, clone(x.next));
  return add_node(x.val + 10 - c, sub_one_digit(x.next, 1));
}


node sub_c(node x, node y, int c)
  requires x::bigint<v1> * y::bigint<v2> & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c> * x::bigint<v1> * y::bigint<v2>;
{
  if (x == null) return null;
  if (y == null) return sub_one_digit(x, c);
  int t = x.val - y.val - c;
  if (t >= 0) {
    //assume false;
      return add_node(t, sub_c(x.next, y.next, 0));
  } else {
    //assume false;
    //assert t+10>0;
  return add_node(t+10, sub_c(x.next, y.next, 1)); 
  }
}

node sub(node x, node y)
  requires x::bigint<v1> * y::bigint<v2> & v1 >= v2
  ensures res::bigint<v1-v2> * x::bigint<v1> * y::bigint<v2>;
{
  return sub_c(x, y, 0);
}

node mult_c(node x, int d, int c)
  requires x::bigint<v> & 0 <= c <= 9 & 0 <= d <= 9 
  ensures res::bigint<v*d+c> * x::bigint<v>;
{
  if (x == null || d==0) {
    if (c==0) return null;
    return new node(c, null);
  } else {
    int ans = x.val * d + c;
    int carry = 0;
    if (ans >= 10) {
      carry = div_with_remainder(ans, 10, ans);
      // carry = ans/10;
      // ans = ans - carry*10;
      // ans = ans%10;
    }
    node rest = mult_c(x.next, d, carry);
    dprint;
    //assume false; 
    return new node(ans, rest);
  }
}

/* left shift all digits one pos (multiplied by ten) */
node shift_left(node x)
  requires x::bigint<v>
  ensures res::bigint<v*10>;
{
  if (x == null) return x;
  return new node(0, x);
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
    return add(t1, t2);
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

bool is_equal(node x, node y)
  requires x::bigint<v1> * y::bigint<v2>
  ensures res & v1 = v2 or !res & v1 != v2;
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

int compare(node x, node y)
  requires x::bigint<v1> * y::bigint<v2>
  ensures res = 0 & v1 = v2 or res = 1 & v1 > v2 or res = -1 & v1 < v2;
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
