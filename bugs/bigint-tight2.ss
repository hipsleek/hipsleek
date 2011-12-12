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

int int_value(node x)
  requires x::bigint<v>
  ensures res = v;


node add_node(int t,node b)
  requires b::bigint<v> & 0<=t<=9
  ensures res::bigint<v*10+t>;


node bigint_of(int v)
  requires v >= 0
  ensures res::bigint<v>;


node add_one_digit(node x, int c)
  requires x::bigint<v> & 0 <= c <= 9
  ensures res::bigint<v+c> * x::bigint<v>;


node add_c(node x, node y, int c)
  requires x::bigint<v1> * y::bigint<v2> & 0 <= c <= 1
  ensures res::bigint<v1+v2+c> * x::bigint<v1> * y::bigint<v2>;


node add(node x, node y)
  requires x::bigint<v1> * y::bigint<v2>
  ensures res::bigint<v1+v2> * x::bigint<v1> * y::bigint<v2>;

node sub_one_digit(node x, int c)
  requires x::bigint<v> & 0 <= c <= 9 & c <= v
  ensures res::bigint<v-c> * x::bigint<v>;



node sub_c(node x, node y, int c)
  requires x::bigint<v1> * y::bigint<v2> & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c> * x::bigint<v1> * y::bigint<v2>;

node sub(node x, node y)
  requires x::bigint<v1> * y::bigint<v2> & v1 >= v2
  ensures res::bigint<v1-v2> * x::bigint<v1> * y::bigint<v2>;


node mult_c(node x, int d, int c)
  requires x::bigint<v> & 0 <= c <= 9 & 0 <= d <= 9 
  ensures res::bigint<v*d+c>; // * x::bigint<v>;
{
  if (x == null || d==0) {
    assume false;
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
      assume false;
    }
    else {
      //assume false;
      assume true;
    }
    node rest = mult_c(x.next, d, carry);
    node rr = new node(ans, rest);
    dprint;
    //assume false; 
    return rr;
  }
}

/* left shift all digits one pos (multiplied by ten) */
node shift_left(node x)
  requires x::bigint<v>
  ensures res::bigint<v*10>;

node mult(node x, node y)
  requires x::bigint<v1> * y::bigint<v2>
  ensures res::bigint<v1*v2> * x::bigint<v1> * y::bigint<v2>;

bool is_zero(node x)
  requires x::bigint<v>
  ensures res & v = 0 or !res & v != 0;


bool is_equal(node x, node y)
  requires x::bigint<v1> * y::bigint<v2>
  ensures res & v1 = v2 or !res & v1 != v2;
/*

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

*/
int div_with_remainder(int a, int b, ref int r)
  requires a >= 0 & b >= 1
  ensures a = b*res + r' & res >= 0 & 0 <= r' <= b-1;

