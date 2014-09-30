data node {
  int val;
  node next;
}

bigint<v> == self = null & v = 0 or
      self::node<p, q> * q::bigint<v1> & 0 <= p <= 9 & v = 10*v1 + p 
      inv v >= 0;

node clone(node x)
  requires x::bigint<v>@L
  ensures res::bigint<v>;
{
  if (x == null) return x;
  return new node(x.val, clone(x.next));
}

int int_value(node x)
  requires x::bigint<v>@L
  ensures res = v;
{
  if (x == null) return 0;
  return x.val + int_value(x.next)*10;
}

node bigint_of(int v)
  requires v >= 0
  ensures res::bigint<v>;
{
  if (v < 10) return new node(v, null);
  int digit = 0;
  int rem = div_with_remainder(v, 10, digit);
  node rest = bigint_of(rem);
  return new node(digit, rest);
}

node add_one_digit(node x, int c)
/*  requires x::bigint<v> & 0 <= c <= 9
  ensures res::bigint<v+c> * x::bigint<v>;*/
  requires x::bigint<v>@L & 0 <= c <= 9
  ensures res::bigint<v+c> ;

{
  if (x == null) return new node(c, x);
  int t = x.val + c;
  if (t >= 10) return new node(t - 10, add_one_digit(x.next, 1));
  return new node(t, clone(x.next));
}


node add_c(node x, node y, int c)
/*
  requires x::bigint<v1> * y::bigint<v2> & 0 <= c <= 1
  ensures res::bigint<v1+v2+c> * x::bigint<v1> * y::bigint<v2>;
*/
/*
  requires x::bigint<v1> * y::bigint<v2> & 0 <= c <= 1
  ensures res::bigint<v1+v2+c> ;

 requires (x::bigint<v1>@I & y::bigint<v2>@I) & 0 <= c <= 1
  ensures res::bigint<v1+v2+c>;

*/
// above should fail but did not

/*
  requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1
  ensures res::bigint<v1+v2+c>;
*/
  requires x::bigint<v1>@L * y::bigint<v2>@L & 0 <= c <= 1
  ensures res::bigint<v1+v2+c>;

{
  if (x == null) {
    if (y == null) {
      if (c == 0) return null;
      else //assume false;
      return new node(c, null);
    } else {
//	    assume false;
      return add_one_digit(y, c);
    }
  } else {
//    assume false;	  
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
//      dprint;
      node rest = add_c(x.next, y.next, carry);
//      dprint;
 //     assume false;
      return new node(t, rest);
    }
  }
}

node add(node x, node y)
  requires x::bigint<v1>@L * y::bigint<v2>@L
  ensures res::bigint<v1+v2>;
/*
  requires x::bigint<v1>@I * y::bigint<v2>@I
  ensures res::bigint<v1+v2>;
*/
{
  return add_c(x, y, 0);
}

node sub_one_digit(node x, int c)
  requires x::bigint<v>@L & 0 <= c <= 9 & c <= v
  ensures res::bigint<v-c>;
{
  if (x == null) return null;
  if (x.val >= c) return new node(x.val - c, clone(x.next));
  return new node(x.val + 10 - c, sub_one_digit(x.next, 1));
}

node sub_c(node x, node y, int c)
/*
  requires (x::bigint<v1>@I) ; y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;

  requires (x::bigint<v1>@I & y::bigint<v2>@I) & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;
  // fails - should succeed

 requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;

  requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;

 requires (y::bigint<v2>@I & x::bigint<v1>@I) & 0 <= c <= 1 & v1 >= v2+c
 ensures res::bigint<v1-v2-c>;
 // fails - should succeed


 requires (y::bigint<v2>@I & x::bigint<v1>@I) & 0 <= c <= 1 & v1 >= v2+c
 ensures res::bigint<v1-v2-c>;

  requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;

 requires (y::bigint<v2>@I & x::bigint<v1>@I) & 0 <= c <= 1 & v1 >= v2+c
 ensures res::bigint<v1-v2-c>;

*/ 

/*
 requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;
*/

 requires y::bigint<v2>@L * x::bigint<v1>@L & 0 <= c <= 1 & v1 >= v2+c
 ensures res::bigint<v1-v2-c>;

{
  //dprint;
  if (x == null) {
    //assume false;
  return null;
  }
  /*
  if (x == null) {
    dprint;
    node r =sub_one_digit(y, c);
    assume false;
    dprint;
    return r;
  }
  */
  //assume false;
  if (y == null) return sub_one_digit(x, c);
  int t = x.val - y.val - c;
  if (t >= 0) return new node(t, sub_c(x.next, y.next, 0));
  return new node(t+10, sub_c(x.next, y.next, 1));
}

node sub(node x, node y)
  requires x::bigint<v1>@L * y::bigint<v2>@L & v1 >= v2
  ensures res::bigint<v1-v2>;
/*
  requires x::bigint<v1>@I * y::bigint<v2>@I & v1 >= v2
  ensures res::bigint<v1-v2>;
*/
{
  return sub_c(x, y, 0);
}

node mult_c(node x, int d, int c)
  requires x::bigint<v>@L & 0 <= c <= 9 & 0 <= d <= 9 
  ensures res::bigint<v*d+c>;
{
  if (x == null) {
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
    return new node(ans, rest);
  }
}

/* left shift all digits one pos (multiplied by ten) */
node shift_left(node x)
  case {
    x=null -> ensures res=null;
   x!=null -> ensures res::node<0,x>;
  }
  /* requires x::bigint<v>@ */
  /* ensures res::bigint<v*10>@I; */
{
  if (x == null) { return x;}
  node t = new node(0, x);
//  dprint;
  return t;
}


node mult(node x, node y)
  requires x::bigint<v1>@L * y::bigint<v2>@L & true
  ensures res::bigint<v1*v2>;

/*
  requires x::bigint<v1>@I * y::bigint<v2>@I
  ensures res::bigint<v1*v2>;
*/
{
  if (x == null || y == null) {
    return null;
  } else {
    node t1 = mult_c(x, y.val, 0);
    node t2 = shift_left(mult(x, y.next));
    return add(t1, t2);
  }
}

/*
node karatsuba_mult(node x, node y)

  requires (x::bigint<v1>@I & y::bigint<v2>@I) 
  ensures res::bigint<v1*v2> ;// x::bigint<v1> * y::bigint<v2>;

  requires x::bigint<v1>@I * y::bigint<v2>@I
  ensures res::bigint<v1*v2> ;// x::bigint<v1> * y::bigint<v2>;

{
  if (x == null || y == null) return null;
  if (x.next == null || y.next == null) return mult(x, y);
  // x = x1*10+x2
  // y = y1*10+y2
  // A = x1*y1
  node A = karatsuba_mult(x.next, y.next);
  // B = x2*y2
  node B = bigint_of(x.val * y.val);
  // C= (x1+x2)*(y1+y2)
  node C = karatsuba_mult(add_one_digit(x.next, x.val), add_one_digit(y.next, y.val));
  // K = C - A - B = x1*y2 + x2*y1
  node K = sub(C, add(A, B));
  // node K = add(mult_c(x.next, y.val, 0), mult_c(y.next, x.val, 0));
  // x * y = A*100 + K*10 + B
  return add(shift_left(shift_left(A)), add(shift_left(K), B));
}
*/

bool is_zero(node x)
  requires x::bigint<v>@L
  ensures true & (res & v = 0 | !res & v != 0);
{
  if (x == null) return true;
  if (x.val == 0 && is_zero(x.next)) return true;
  return false;
}

bool is_equal(node x, node y)
  requires x::bigint<v1>@L * y::bigint<v2>@L
  ensures true & (res & v1 = v2 | !res & v1 != v2);
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

int compare2(node x, node y)
  requires x::bigint<v1>@L * y::bigint<v2>@L
  ensures true & (res = 0 & v1 = v2 | res = 1 & v1 > v2 | res = -1 & v1 < v2);

{
  if (x == null) {
    if (is_zero(y)) return 0;
    return -1;
  }
  if (y == null) {
    if (is_zero(x)) return 0;
    return 1;
  }
  int c = compare2(x.next, y.next);
  if (c == 0) return compare_int(x.val, y.val);
  return c;
}

int compare_int(int x, int y)
  requires true
  ensures true & (res = 0 & x = y | res = 1 & x > y | res = -1 & x < y);
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
